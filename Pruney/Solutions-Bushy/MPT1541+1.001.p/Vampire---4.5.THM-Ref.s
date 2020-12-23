%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1541+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:03 EST 2020

% Result     : Theorem 3.15s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  345 (2747 expanded)
%              Number of leaves         :   31 ( 930 expanded)
%              Depth                    :   50
%              Number of atoms          : 2622 (35621 expanded)
%              Number of equality atoms :   99 (2571 expanded)
%              Maximal formula depth    :   25 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f188,f252,f329,f926,f1002,f1585,f1626,f1643,f1929,f3469,f3494])).

fof(f3494,plain,
    ( spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f3493])).

fof(f3493,plain,
    ( $false
    | spl11_2
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f93,f1258])).

fof(f1258,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1257,f1112])).

fof(f1112,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1108,f51])).

fof(f51,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
          | k11_lattice3(sK3,sK4,sK5) != sK6 )
        & ! [X4] :
            ( r1_orders_2(sK3,X4,sK6)
            | ~ r1_orders_2(sK3,X4,sK5)
            | ~ r1_orders_2(sK3,X4,sK4)
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        & r1_orders_2(sK3,sK6,sK5)
        & r1_orders_2(sK3,sK6,sK4) )
      | sP0(sK6,sK3,sK5,sK4) )
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                          | k11_lattice3(X0,X1,X2) != X3 )
                        & ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | sP0(X3,X0,X2,X1) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(X1,X2))
                        | k11_lattice3(sK3,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(sK3,X4,X3)
                          | ~ r1_orders_2(sK3,X4,X2)
                          | ~ r1_orders_2(sK3,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
                      & r1_orders_2(sK3,X3,X2)
                      & r1_orders_2(sK3,X3,X1) )
                    | sP0(X3,sK3,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(X1,X2))
                      | k11_lattice3(sK3,X1,X2) != X3 )
                    & ! [X4] :
                        ( r1_orders_2(sK3,X4,X3)
                        | ~ r1_orders_2(sK3,X4,X2)
                        | ~ r1_orders_2(sK3,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
                    & r1_orders_2(sK3,X3,X2)
                    & r1_orders_2(sK3,X3,X1) )
                  | sP0(X3,sK3,X2,X1) )
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,X2))
                    | k11_lattice3(sK3,sK4,X2) != X3 )
                  & ! [X4] :
                      ( r1_orders_2(sK3,X4,X3)
                      | ~ r1_orders_2(sK3,X4,X2)
                      | ~ r1_orders_2(sK3,X4,sK4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
                  & r1_orders_2(sK3,X3,X2)
                  & r1_orders_2(sK3,X3,sK4) )
                | sP0(X3,sK3,X2,sK4) )
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,X2))
                  | k11_lattice3(sK3,sK4,X2) != X3 )
                & ! [X4] :
                    ( r1_orders_2(sK3,X4,X3)
                    | ~ r1_orders_2(sK3,X4,X2)
                    | ~ r1_orders_2(sK3,X4,sK4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
                & r1_orders_2(sK3,X3,X2)
                & r1_orders_2(sK3,X3,sK4) )
              | sP0(X3,sK3,X2,sK4) )
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ? [X3] :
          ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
                | k11_lattice3(sK3,sK4,sK5) != X3 )
              & ! [X4] :
                  ( r1_orders_2(sK3,X4,X3)
                  | ~ r1_orders_2(sK3,X4,sK5)
                  | ~ r1_orders_2(sK3,X4,sK4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
              & r1_orders_2(sK3,X3,sK5)
              & r1_orders_2(sK3,X3,sK4) )
            | sP0(X3,sK3,sK5,sK4) )
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
              | k11_lattice3(sK3,sK4,sK5) != X3 )
            & ! [X4] :
                ( r1_orders_2(sK3,X4,X3)
                | ~ r1_orders_2(sK3,X4,sK5)
                | ~ r1_orders_2(sK3,X4,sK4)
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            & r1_orders_2(sK3,X3,sK5)
            & r1_orders_2(sK3,X3,sK4) )
          | sP0(X3,sK3,sK5,sK4) )
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
            | k11_lattice3(sK3,sK4,sK5) != sK6 )
          & ! [X4] :
              ( r1_orders_2(sK3,X4,sK6)
              | ~ r1_orders_2(sK3,X4,sK5)
              | ~ r1_orders_2(sK3,X4,sK4)
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          & r1_orders_2(sK3,sK6,sK5)
          & r1_orders_2(sK3,sK6,sK4) )
        | sP0(sK6,sK3,sK5,sK4) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | sP0(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f20])).

fof(f20,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP0(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) )
                       => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X5,X2)
                                  & r1_orders_2(X0,X5,X1) )
                               => r1_orders_2(X0,X5,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) )
                       => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                          & k11_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_0)).

fof(f1108,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1107,f52])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1107,plain,
    ( ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1106,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1106,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1104,f53])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1104,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl11_7 ),
    inference(resolution,[],[f1071,f799])).

fof(f799,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f798,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f798,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f797,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f86,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f797,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f793,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f87,f84])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f793,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ v5_orders_2(X3)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f783])).

fof(f783,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f642,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f22])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_lattice3)).

fof(f642,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f641,f84])).

fof(f641,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f640,f117])).

fof(f640,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f628])).

fof(f628,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f379,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f379,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(subsumption_resolution,[],[f378,f84])).

fof(f378,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(subsumption_resolution,[],[f368,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0))
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f368,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ m1_subset_1(sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),u1_struct_0(X18))
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ m1_subset_1(sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),u1_struct_0(X18))
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18)
      | ~ l1_orders_2(X18) ) ),
    inference(resolution,[],[f195,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ sP1(X0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f85,f84])).

fof(f85,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k11_lattice3(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1071,plain,
    ( sP1(sK3,sK4,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl11_7
  <=> sP1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1257,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1256,f55])).

fof(f55,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1256,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1255,f108])).

fof(f108,plain,
    ( r1_orders_2(sK3,sK6,sK4)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_6
  <=> r1_orders_2(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1255,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1254,f104])).

fof(f104,plain,
    ( r1_orders_2(sK3,sK6,sK5)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_5
  <=> r1_orders_2(sK3,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1254,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(duplicate_literal_removal,[],[f1244])).

fof(f1244,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(resolution,[],[f1113,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1113,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1047,f1112])).

fof(f1047,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f1046])).

fof(f1046,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl11_4 ),
    inference(resolution,[],[f1010,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1010,plain,
    ( ! [X8,X9] :
        ( ~ r1_orders_2(sK3,sK7(sK3,sK5,X8,X9),sK4)
        | r1_orders_2(sK3,sK7(sK3,sK5,X8,X9),sK6)
        | k11_lattice3(sK3,X8,sK5) = X9
        | ~ r1_orders_2(sK3,X9,sK5)
        | ~ r1_orders_2(sK3,X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,X8) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f992,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f992,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(sK7(sK3,sK5,X8,X9),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,X8,X9),sK4)
        | r1_orders_2(sK3,sK7(sK3,sK5,X8,X9),sK6)
        | k11_lattice3(sK3,X8,sK5) = X9
        | ~ r1_orders_2(sK3,X9,sK5)
        | ~ r1_orders_2(sK3,X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,X8) )
    | ~ spl11_4 ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,
    ( ! [X4] :
        ( ~ r1_orders_2(sK3,X4,sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X4,sK4)
        | r1_orders_2(sK3,X4,sK6) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl11_4
  <=> ! [X4] :
        ( r1_orders_2(sK3,X4,sK6)
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X4,sK4)
        | ~ r1_orders_2(sK3,X4,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f93,plain,
    ( k11_lattice3(sK3,sK4,sK5) != sK6
    | spl11_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl11_2
  <=> k11_lattice3(sK3,sK4,sK5) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f3469,plain,
    ( spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f3468])).

fof(f3468,plain,
    ( $false
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3467,f52])).

fof(f3467,plain,
    ( ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3466,f55])).

fof(f3466,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3465,f53])).

fof(f3465,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3464,f54])).

fof(f3464,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3463,f108])).

fof(f3463,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3462,f104])).

fof(f3462,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(resolution,[],[f3334,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f3334,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f3333,f55])).

fof(f3333,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f3332,f1603])).

fof(f1603,plain,
    ( sK6 = k11_lattice3(sK3,sK6,sK4)
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f1602,plain,
    ( spl11_33
  <=> sK6 = k11_lattice3(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f3332,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f3331,f1603])).

fof(f3331,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3330,f54])).

fof(f3330,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3329,f51])).

fof(f3329,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3328,f96])).

fof(f96,plain,
    ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl11_3
  <=> r2_yellow_0(sK3,k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f3328,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3327,f52])).

fof(f3327,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3326,f55])).

fof(f3326,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3325,f53])).

fof(f3325,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3324,f1088])).

fof(f1088,plain,
    ( sP1(sK3,sK4,sK6)
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1087,f51])).

fof(f1087,plain,
    ( sP1(sK3,sK4,sK6)
    | ~ v5_orders_2(sK3)
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1086,f52])).

fof(f1086,plain,
    ( ~ l1_orders_2(sK3)
    | sP1(sK3,sK4,sK6)
    | ~ v5_orders_2(sK3)
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1085,f53])).

fof(f1085,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK4,sK6)
    | ~ v5_orders_2(sK3)
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1083,f55])).

fof(f1083,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK4,sK6)
    | ~ v5_orders_2(sK3)
    | ~ spl11_13 ),
    inference(resolution,[],[f328,f799])).

fof(f328,plain,
    ( sP1(sK3,sK6,sK4)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl11_13
  <=> sP1(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f3324,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f3304])).

fof(f3304,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),k11_lattice3(sK3,sK6,sK4))
    | ~ v5_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f1574,f539])).

fof(f539,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK9(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f538,f84])).

fof(f538,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK9(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f526])).

fof(f526,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK9(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k11_lattice3(X0,X3,X1))
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f381,f147])).

fof(f147,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK9(X0,X1,X2))
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK10(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK10(X0,X1))
              & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK10(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK10(X0,X1))
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f144,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f71,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f381,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ v5_orders_2(X23) ) ),
    inference(subsumption_resolution,[],[f380,f84])).

fof(f380,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ v5_orders_2(X23) ) ),
    inference(subsumption_resolution,[],[f367,f80])).

fof(f367,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ m1_subset_1(sK9(X23,X24,k11_lattice3(X23,X25,X26)),u1_struct_0(X23))
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ v5_orders_2(X23) ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ m1_subset_1(sK9(X23,X24,k11_lattice3(X23,X25,X26)),u1_struct_0(X23))
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | ~ v5_orders_2(X23) ) ),
    inference(resolution,[],[f195,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1574,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1573,f51])).

fof(f1573,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1572,f52])).

fof(f1572,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1571,f96])).

fof(f1571,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | spl11_3
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f1570])).

fof(f1570,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f1343,f80])).

fof(f1343,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl11_3
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f1342,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1342,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1341,f96])).

fof(f1341,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f1340,f83])).

fof(f1340,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f1339,f83])).

fof(f1339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f1338,f83])).

fof(f1338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1337,f51])).

fof(f1337,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1336,f52])).

fof(f1336,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1335,f54])).

fof(f1335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1334,f53])).

fof(f1334,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f1331])).

fof(f1331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(resolution,[],[f1019,f157])).

fof(f157,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f154,f80])).

fof(f154,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f72,f81])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1019,plain,
    ( ! [X14,X15] :
        ( ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK4)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X14),X15),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK6)
        | ~ m1_subset_1(X14,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,X14))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X14),X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK3)) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1018,f51])).

fof(f1018,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X14),X15),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK6)
        | ~ m1_subset_1(X14,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,X14))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X14),X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1017,f52])).

fof(f1017,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X14),X15),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK6)
        | ~ m1_subset_1(X14,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK5,X14))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X14),X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f995,f54])).

fof(f995,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X14),X15),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X14),X15),sK6)
        | ~ m1_subset_1(X14,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK5,X14))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X14),X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(resolution,[],[f100,f147])).

fof(f1929,plain,(
    spl11_32 ),
    inference(avatar_contradiction_clause,[],[f1928])).

fof(f1928,plain,
    ( $false
    | spl11_32 ),
    inference(subsumption_resolution,[],[f1927,f52])).

fof(f1927,plain,
    ( ~ l1_orders_2(sK3)
    | spl11_32 ),
    inference(subsumption_resolution,[],[f1926,f55])).

fof(f1926,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_32 ),
    inference(subsumption_resolution,[],[f1920,f53])).

fof(f1920,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_32 ),
    inference(resolution,[],[f1600,f84])).

fof(f1600,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | spl11_32 ),
    inference(avatar_component_clause,[],[f1599])).

fof(f1599,plain,
    ( spl11_32
  <=> m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f1643,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | spl11_27 ),
    inference(avatar_contradiction_clause,[],[f1642])).

fof(f1642,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_13
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1641,f1088])).

fof(f1641,plain,
    ( ~ sP1(sK3,sK4,sK6)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1640,f55])).

fof(f1640,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1639,f1000])).

fof(f1000,plain,
    ( r1_orders_2(sK3,sK6,sK6)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f999,f108])).

fof(f999,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | r1_orders_2(sK3,sK6,sK6)
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f986,f55])).

fof(f986,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | r1_orders_2(sK3,sK6,sK6)
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(resolution,[],[f100,f104])).

fof(f1639,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | ~ spl11_5
    | ~ spl11_6
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1638,f108])).

fof(f1638,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | ~ spl11_5
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1635,f104])).

fof(f1635,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK6)
    | spl11_27 ),
    inference(superposition,[],[f1162,f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP1(X0,X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP1(X0,X2,X1)
      | k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f66,f64])).

fof(f1162,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | spl11_27 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl11_27
  <=> r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f1626,plain,
    ( ~ spl11_27
    | ~ spl11_32
    | ~ spl11_28
    | spl11_33
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f1625,f327,f186,f183,f107,f103,f1602,f1164,f1599,f1161])).

fof(f1164,plain,
    ( spl11_28
  <=> r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f186,plain,
    ( spl11_8
  <=> ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK7(sK3,sK4,sK5,X0),sK6)
        | k11_lattice3(sK3,sK5,sK4) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1625,plain,
    ( sK6 = k11_lattice3(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(forward_demodulation,[],[f1624,f1218])).

fof(f1218,plain,
    ( sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f1217,f1071])).

fof(f1217,plain,
    ( sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f1216,f104])).

fof(f1216,plain,
    ( sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f1215,f55])).

fof(f1215,plain,
    ( sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f1214,f108])).

fof(f1214,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f1204])).

fof(f1204,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sK6 = k11_lattice3(sK3,sK5,sK4)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8 ),
    inference(resolution,[],[f187,f66])).

fof(f187,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK4,sK5,X0),sK6)
        | ~ r1_orders_2(sK3,X0,sK4)
        | k11_lattice3(sK3,sK5,sK4) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK5) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1624,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1623,f1071])).

fof(f1623,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1622,f52])).

fof(f1622,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1621,f55])).

fof(f1621,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1620,f53])).

fof(f1620,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f1211,f1088])).

fof(f1211,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ sP1(sK3,sK4,sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f1207])).

fof(f1207,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK4),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ sP1(sK3,sK4,sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k11_lattice3(sK3,sK5,sK4) = k11_lattice3(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK5)
    | ~ sP1(sK3,sK4,sK5)
    | ~ spl11_8 ),
    inference(resolution,[],[f187,f625])).

fof(f625,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK7(X4,X5,X6,k11_lattice3(X4,X7,X5)),X7)
      | ~ sP1(X4,X5,X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k11_lattice3(X4,X7,X5) = k11_lattice3(X4,X6,X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X6)
      | ~ sP1(X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f624,f84])).

fof(f624,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK7(X4,X5,X6,k11_lattice3(X4,X7,X5)),X7)
      | ~ sP1(X4,X5,X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k11_lattice3(X4,X7,X5) = k11_lattice3(X4,X6,X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X6)
      | ~ sP1(X4,X5,X6)
      | ~ m1_subset_1(k11_lattice3(X4,X7,X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f620,f117])).

fof(f620,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK7(X4,X5,X6,k11_lattice3(X4,X7,X5)),X7)
      | ~ sP1(X4,X5,X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k11_lattice3(X4,X7,X5) = k11_lattice3(X4,X6,X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X6)
      | ~ sP1(X4,X5,X6)
      | ~ m1_subset_1(k11_lattice3(X4,X7,X5),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f610])).

fof(f610,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK7(X4,X5,X6,k11_lattice3(X4,X7,X5)),X7)
      | ~ sP1(X4,X5,X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k11_lattice3(X4,X7,X5) = k11_lattice3(X4,X6,X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X6)
      | ~ sP1(X4,X5,X6)
      | k11_lattice3(X4,X7,X5) = k11_lattice3(X4,X6,X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X7,X5),X6)
      | ~ m1_subset_1(k11_lattice3(X4,X7,X5),u1_struct_0(X4))
      | ~ sP1(X4,X5,X6) ) ),
    inference(resolution,[],[f377,f65])).

fof(f377,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X16,X17) = k11_lattice3(X13,X15,X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ sP1(X13,X14,X15) ) ),
    inference(subsumption_resolution,[],[f376,f84])).

fof(f376,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X16,X17) = k11_lattice3(X13,X15,X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ m1_subset_1(k11_lattice3(X13,X16,X17),u1_struct_0(X13))
      | ~ sP1(X13,X14,X15) ) ),
    inference(subsumption_resolution,[],[f359,f63])).

fof(f359,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ m1_subset_1(sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),u1_struct_0(X13))
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X16,X17) = k11_lattice3(X13,X15,X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ m1_subset_1(k11_lattice3(X13,X16,X17),u1_struct_0(X13))
      | ~ sP1(X13,X14,X15) ) ),
    inference(resolution,[],[f195,f66])).

fof(f1585,plain,
    ( ~ spl11_13
    | spl11_28 ),
    inference(avatar_contradiction_clause,[],[f1584])).

fof(f1584,plain,
    ( $false
    | ~ spl11_13
    | spl11_28 ),
    inference(subsumption_resolution,[],[f1583,f52])).

fof(f1583,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl11_13
    | spl11_28 ),
    inference(subsumption_resolution,[],[f1582,f55])).

fof(f1582,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl11_13
    | spl11_28 ),
    inference(subsumption_resolution,[],[f1581,f53])).

fof(f1581,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl11_13
    | spl11_28 ),
    inference(subsumption_resolution,[],[f1575,f1088])).

fof(f1575,plain,
    ( ~ sP1(sK3,sK4,sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl11_28 ),
    inference(resolution,[],[f1165,f117])).

fof(f1165,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK4),sK4)
    | spl11_28 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1002,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_12 ),
    inference(avatar_contradiction_clause,[],[f1001])).

fof(f1001,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1000,f320])).

fof(f320,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl11_12
  <=> r1_orders_2(sK3,sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f926,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f924,f921])).

fof(f921,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f917,f54])).

fof(f917,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f916,f52])).

fof(f916,plain,
    ( ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f915,f51])).

fof(f915,plain,
    ( ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f908,f53])).

fof(f908,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1 ),
    inference(resolution,[],[f903,f259])).

fof(f259,plain,
    ( r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl11_1 ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r2_yellow_0(X1,k2_tarski(X3,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
            & r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
            & r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
            & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X1,X4,X0)
              & r1_orders_2(X1,X4,X2)
              & r1_orders_2(X1,X4,X3)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP0(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f90,plain,
    ( sP0(sK6,sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_1
  <=> sP0(sK6,sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f903,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f902,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f902,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f901,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f155,f77])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f72,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK10(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f901,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f900,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f145,f77])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f71,f78])).

fof(f900,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f891])).

fof(f891,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP1(X1,X0,X2)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f681,f68])).

fof(f681,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f680,f77])).

fof(f680,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f679,f156])).

fof(f679,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f675,f67])).

fof(f675,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ m1_subset_1(sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f668])).

fof(f668,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ m1_subset_1(sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | sP1(X4,X6,X7)
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f426,f69])).

fof(f426,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP1(X0,X3,X4)
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP1(X0,X3,X4)
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f220,f73])).

fof(f220,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | sP1(X6,X7,X8)
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(subsumption_resolution,[],[f217,f77])).

fof(f217,plain,(
    ! [X6,X8,X7,X9] :
      ( sP1(X6,X7,X8)
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(sK10(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X6,X8,X7,X9] :
      ( sP1(X6,X7,X8)
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(sK10(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9)
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK10(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f924,plain,
    ( ~ sP1(sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f923,f52])).

fof(f923,plain,
    ( ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f922,f53])).

fof(f922,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f802,f54])).

fof(f802,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl11_1 ),
    inference(resolution,[],[f771,f90])).

fof(f771,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X9,X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ sP1(X6,X8,X7) ) ),
    inference(duplicate_literal_removal,[],[f770])).

fof(f770,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X9,X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ sP1(X6,X8,X7)
      | ~ sP0(X9,X6,X8,X7) ) ),
    inference(superposition,[],[f763,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X1,X3,X2) = X0
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f763,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f762,f261])).

fof(f261,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X0,X2,X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X2) ) ),
    inference(superposition,[],[f117,f45])).

fof(f762,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1) ) ),
    inference(subsumption_resolution,[],[f761,f262])).

fof(f262,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X0,X2,X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X1) ) ),
    inference(superposition,[],[f119,f45])).

fof(f761,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f749])).

fof(f749,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2) ) ),
    inference(resolution,[],[f584,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f584,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(subsumption_resolution,[],[f581,f117])).

fof(f581,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(resolution,[],[f375,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f375,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X10)
      | ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X9)
      | ~ sP1(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X12)
      | ~ sP0(k11_lattice3(X8,X9,X10),X8,X11,X12) ) ),
    inference(subsumption_resolution,[],[f358,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f358,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X9)
      | ~ m1_subset_1(sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),u1_struct_0(X8))
      | ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X10)
      | ~ sP1(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X12)
      | ~ sP0(k11_lattice3(X8,X9,X10),X8,X11,X12) ) ),
    inference(resolution,[],[f195,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f329,plain,
    ( spl11_13
    | ~ spl11_12
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f325,f107,f319,f327])).

fof(f325,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK4)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f324,f52])).

fof(f324,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK4)
    | ~ l1_orders_2(sK3)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f323,f51])).

fof(f323,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK4)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f322,f53])).

fof(f322,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f296,f55])).

fof(f296,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_6 ),
    inference(resolution,[],[f218,f108])).

fof(f218,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | ~ r1_orders_2(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | sP1(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | ~ r1_orders_2(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f70,f69])).

fof(f252,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f250,f52])).

fof(f250,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f249,f51])).

fof(f249,plain,
    ( ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f248,f54])).

fof(f248,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f247,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f246,f184])).

fof(f184,plain,
    ( ~ sP1(sK3,sK4,sK5)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f246,plain,
    ( sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f245,f104])).

fof(f245,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | ~ spl11_6
    | spl11_7 ),
    inference(subsumption_resolution,[],[f244,f108])).

fof(f244,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f243,f55])).

fof(f243,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | spl11_7 ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl11_4
    | spl11_7 ),
    inference(resolution,[],[f241,f70])).

fof(f241,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f240,f52])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f238,f54])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f237,f53])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f236,f184])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(resolution,[],[f227,f67])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f226,f52])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f225,f51])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f223,f184])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f222,f53])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl11_4 ),
    inference(resolution,[],[f200,f69])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | sP1(sK3,X0,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f199,f52])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f198,f51])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f197,f54])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl11_4 ),
    inference(resolution,[],[f68,f100])).

fof(f188,plain,
    ( ~ spl11_7
    | spl11_8
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f181,f99,f186,f183])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK4,sK5)
        | k11_lattice3(sK3,sK5,sK4) = X0
        | r1_orders_2(sK3,sK7(sK3,sK4,sK5,X0),sK6) )
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK4,sK5)
        | k11_lattice3(sK3,sK5,sK4) = X0
        | r1_orders_2(sK3,sK7(sK3,sK4,sK5,X0),sK6)
        | k11_lattice3(sK3,sK5,sK4) = X0
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK4,sK5) )
    | ~ spl11_4 ),
    inference(resolution,[],[f177,f65])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,sK7(sK3,X0,sK5,X1),sK4)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP1(sK3,X0,sK5)
        | k11_lattice3(sK3,sK5,X0) = X1
        | r1_orders_2(sK3,sK7(sK3,X0,sK5,X1),sK6) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK3,sK5,X0) = X1
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP1(sK3,X0,sK5)
        | ~ m1_subset_1(sK7(sK3,X0,sK5,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK7(sK3,X0,sK5,X1),sK4)
        | r1_orders_2(sK3,sK7(sK3,X0,sK5,X1),sK6) )
    | ~ spl11_4 ),
    inference(resolution,[],[f64,f100])).

fof(f109,plain,
    ( spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f56,f107,f89])).

fof(f56,plain,
    ( r1_orders_2(sK3,sK6,sK4)
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,
    ( spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f57,f103,f89])).

fof(f57,plain,
    ( r1_orders_2(sK3,sK6,sK5)
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,
    ( spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f58,f99,f89])).

fof(f58,plain,(
    ! [X4] :
      ( r1_orders_2(sK3,X4,sK6)
      | ~ r1_orders_2(sK3,X4,sK5)
      | ~ r1_orders_2(sK3,X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP0(sK6,sK3,sK5,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f59,f95,f92,f89])).

fof(f59,plain,
    ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | k11_lattice3(sK3,sK4,sK5) != sK6
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
