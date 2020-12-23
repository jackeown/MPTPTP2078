%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1545+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:04 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  197 (1889 expanded)
%              Number of leaves         :   26 ( 721 expanded)
%              Depth                    :   50
%              Number of atoms          : 1566 (29054 expanded)
%              Number of equality atoms :   86 (1880 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f115,f117,f119,f1801,f1900,f1942,f2454])).

fof(f2454,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f2453])).

fof(f2453,plain,
    ( $false
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2452,f46])).

fof(f46,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( ~ r1_orders_2(sK1,sK5,sK4)
        & r1_orders_2(sK1,sK5,sK3)
        & r1_orders_2(sK1,sK5,sK2)
        & m1_subset_1(sK5,u1_struct_0(sK1)) )
      | ~ r1_orders_2(sK1,sK4,sK3)
      | ~ r1_orders_2(sK1,sK4,sK2)
      | k12_lattice3(sK1,sK2,sK3) != sK4 )
    & ( ( ! [X5] :
            ( r1_orders_2(sK1,X5,sK4)
            | ~ r1_orders_2(sK1,X5,sK3)
            | ~ r1_orders_2(sK1,X5,sK2)
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & r1_orders_2(sK1,sK4,sK3)
        & r1_orders_2(sK1,sK4,sK2) )
      | k12_lattice3(sK1,sK2,sK3) = sK4 )
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f25,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | k12_lattice3(X0,X1,X2) != X3 )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) = X3 )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(sK1,X4,X3)
                        & r1_orders_2(sK1,X4,X2)
                        & r1_orders_2(sK1,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(sK1)) )
                    | ~ r1_orders_2(sK1,X3,X2)
                    | ~ r1_orders_2(sK1,X3,X1)
                    | k12_lattice3(sK1,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(sK1,X5,X3)
                          | ~ r1_orders_2(sK1,X5,X2)
                          | ~ r1_orders_2(sK1,X5,X1)
                          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                      & r1_orders_2(sK1,X3,X2)
                      & r1_orders_2(sK1,X3,X1) )
                    | k12_lattice3(sK1,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ? [X4] :
                      ( ~ r1_orders_2(sK1,X4,X3)
                      & r1_orders_2(sK1,X4,X2)
                      & r1_orders_2(sK1,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(sK1)) )
                  | ~ r1_orders_2(sK1,X3,X2)
                  | ~ r1_orders_2(sK1,X3,X1)
                  | k12_lattice3(sK1,X1,X2) != X3 )
                & ( ( ! [X5] :
                        ( r1_orders_2(sK1,X5,X3)
                        | ~ r1_orders_2(sK1,X5,X2)
                        | ~ r1_orders_2(sK1,X5,X1)
                        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                    & r1_orders_2(sK1,X3,X2)
                    & r1_orders_2(sK1,X3,X1) )
                  | k12_lattice3(sK1,X1,X2) = X3 )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ? [X4] :
                    ( ~ r1_orders_2(sK1,X4,X3)
                    & r1_orders_2(sK1,X4,X2)
                    & r1_orders_2(sK1,X4,sK2)
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ r1_orders_2(sK1,X3,X2)
                | ~ r1_orders_2(sK1,X3,sK2)
                | k12_lattice3(sK1,sK2,X2) != X3 )
              & ( ( ! [X5] :
                      ( r1_orders_2(sK1,X5,X3)
                      | ~ r1_orders_2(sK1,X5,X2)
                      | ~ r1_orders_2(sK1,X5,sK2)
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                  & r1_orders_2(sK1,X3,X2)
                  & r1_orders_2(sK1,X3,sK2) )
                | k12_lattice3(sK1,sK2,X2) = X3 )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_orders_2(sK1,X4,X3)
                  & r1_orders_2(sK1,X4,X2)
                  & r1_orders_2(sK1,X4,sK2)
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              | ~ r1_orders_2(sK1,X3,X2)
              | ~ r1_orders_2(sK1,X3,sK2)
              | k12_lattice3(sK1,sK2,X2) != X3 )
            & ( ( ! [X5] :
                    ( r1_orders_2(sK1,X5,X3)
                    | ~ r1_orders_2(sK1,X5,X2)
                    | ~ r1_orders_2(sK1,X5,sK2)
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                & r1_orders_2(sK1,X3,X2)
                & r1_orders_2(sK1,X3,sK2) )
              | k12_lattice3(sK1,sK2,X2) = X3 )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_orders_2(sK1,X4,X3)
                & r1_orders_2(sK1,X4,sK3)
                & r1_orders_2(sK1,X4,sK2)
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ r1_orders_2(sK1,X3,sK3)
            | ~ r1_orders_2(sK1,X3,sK2)
            | k12_lattice3(sK1,sK2,sK3) != X3 )
          & ( ( ! [X5] :
                  ( r1_orders_2(sK1,X5,X3)
                  | ~ r1_orders_2(sK1,X5,sK3)
                  | ~ r1_orders_2(sK1,X5,sK2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & r1_orders_2(sK1,X3,sK3)
              & r1_orders_2(sK1,X3,sK2) )
            | k12_lattice3(sK1,sK2,sK3) = X3 )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( ~ r1_orders_2(sK1,X4,X3)
              & r1_orders_2(sK1,X4,sK3)
              & r1_orders_2(sK1,X4,sK2)
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ r1_orders_2(sK1,X3,sK3)
          | ~ r1_orders_2(sK1,X3,sK2)
          | k12_lattice3(sK1,sK2,sK3) != X3 )
        & ( ( ! [X5] :
                ( r1_orders_2(sK1,X5,X3)
                | ~ r1_orders_2(sK1,X5,sK3)
                | ~ r1_orders_2(sK1,X5,sK2)
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & r1_orders_2(sK1,X3,sK3)
            & r1_orders_2(sK1,X3,sK2) )
          | k12_lattice3(sK1,sK2,sK3) = X3 )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ( ? [X4] :
            ( ~ r1_orders_2(sK1,X4,sK4)
            & r1_orders_2(sK1,X4,sK3)
            & r1_orders_2(sK1,X4,sK2)
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        | ~ r1_orders_2(sK1,sK4,sK3)
        | ~ r1_orders_2(sK1,sK4,sK2)
        | k12_lattice3(sK1,sK2,sK3) != sK4 )
      & ( ( ! [X5] :
              ( r1_orders_2(sK1,X5,sK4)
              | ~ r1_orders_2(sK1,X5,sK3)
              | ~ r1_orders_2(sK1,X5,sK2)
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & r1_orders_2(sK1,sK4,sK3)
          & r1_orders_2(sK1,sK4,sK2) )
        | k12_lattice3(sK1,sK2,sK3) = sK4 )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ~ r1_orders_2(sK1,X4,sK4)
        & r1_orders_2(sK1,X4,sK3)
        & r1_orders_2(sK1,X4,sK2)
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ~ r1_orders_2(sK1,sK5,sK4)
      & r1_orders_2(sK1,sK5,sK3)
      & r1_orders_2(sK1,sK5,sK2)
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X5,X3)
                          | ~ r1_orders_2(X0,X5,X2)
                          | ~ r1_orders_2(X0,X5,X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r1_orders_2(X0,X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r1_orders_2(X0,X3,X1)
                    | k12_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | k12_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k12_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f2452,plain,
    ( ~ v5_orders_2(sK1)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2451,f47])).

fof(f47,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2451,plain,
    ( ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2450,f48])).

fof(f48,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2450,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2449,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2449,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2448,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2448,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2402,f88])).

fof(f88,plain,
    ( k12_lattice3(sK1,sK2,sK3) != sK4
    | spl12_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl12_1
  <=> k12_lattice3(sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f2402,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(superposition,[],[f81,f2356])).

fof(f2356,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2355,f46])).

fof(f2355,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2354,f47])).

fof(f2354,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2353,f48])).

fof(f2353,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2352,f50])).

fof(f2352,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2327,f49])).

fof(f2327,plain,
    ( sK4 = k12_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(superposition,[],[f2209,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f2209,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2208,f1790])).

fof(f1790,plain,(
    sP0(sK1,sK2,sK3) ),
    inference(resolution,[],[f1755,f50])).

fof(f1755,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | sP0(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f1754,f47])).

fof(f1754,plain,(
    ! [X0] :
      ( sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1753,f48])).

fof(f1753,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1735,f46])).

fof(f1735,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK1)
      | ~ l1_orders_2(sK1)
      | sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1) ) ),
    inference(resolution,[],[f1734,f49])).

fof(f1734,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v2_lattice3(X1) ) ),
    inference(subsumption_resolution,[],[f1733,f70])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,sK10(X0,X3),X3)
                  & r1_orders_2(X0,sK10(X0,X3),sK9(X0))
                  & r1_orders_2(X0,sK10(X0,X3),sK8(X0))
                  & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,sK9(X0))
                | ~ r1_orders_2(X0,X3,sK8(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,X8,sK11(X0,X5,X6))
                        | ~ r1_orders_2(X0,X8,X6)
                        | ~ r1_orders_2(X0,X8,X5)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,sK11(X0,X5,X6),X6)
                    & r1_orders_2(X0,sK11(X0,X5,X6),X5)
                    & m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f40,f44,f43,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r1_orders_2(X0,X4,sK8(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK8(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r1_orders_2(X0,X4,sK8(X0))
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_orders_2(X0,X3,sK8(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK9(X0))
                & r1_orders_2(X0,X4,sK8(X0))
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK9(X0))
            | ~ r1_orders_2(X0,X3,sK8(X0))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,sK9(X0))
          & r1_orders_2(X0,X4,sK8(X0))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK10(X0,X3),X3)
        & r1_orders_2(X0,sK10(X0,X3),sK9(X0))
        & r1_orders_2(X0,sK10(X0,X3),sK8(X0))
        & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X8,X7)
              | ~ r1_orders_2(X0,X8,X6)
              | ~ r1_orders_2(X0,X8,X5)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,X8,sK11(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK11(X0,X5,X6),X6)
        & r1_orders_2(X0,sK11(X0,X5,X6),X5)
        & m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X8,X7)
                          | ~ r1_orders_2(X0,X8,X6)
                          | ~ r1_orders_2(X0,X8,X5)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X7,X6)
                      & r1_orders_2(X0,X7,X5)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattice3)).

fof(f1733,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v2_lattice3(X1)
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1732,f72])).

fof(f72,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK11(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1732,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v2_lattice3(X1)
      | ~ r1_orders_2(X1,sK11(X1,X2,X0),X0)
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1731,f71])).

fof(f71,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK11(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1731,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v2_lattice3(X1)
      | ~ r1_orders_2(X1,sK11(X1,X2,X0),X2)
      | ~ r1_orders_2(X1,sK11(X1,X2,X0),X0)
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1722])).

fof(f1722,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v2_lattice3(X1)
      | sP0(X1,X2,X0)
      | ~ r1_orders_2(X1,sK11(X1,X2,X0),X2)
      | ~ r1_orders_2(X1,sK11(X1,X2,X0),X0)
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f818,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
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
    inference(definition_folding,[],[f12,f21])).

fof(f21,plain,(
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
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_lattice3)).

fof(f818,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v2_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f817,f70])).

fof(f817,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f816,f72])).

fof(f816,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X5)
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f811,f71])).

fof(f811,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X3)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X5)
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f802])).

fof(f802,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X3)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X3)
      | ~ r1_orders_2(X4,sK11(X4,X3,X5),X5)
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f382,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f382,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X2,X3,sK11(X0,X1,X2)),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X3,X2)
      | ~ r1_orders_2(X0,sK11(X0,X1,X2),X3)
      | ~ m1_subset_1(sK7(X0,X2,X3,sK11(X0,X1,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f381,f70])).

fof(f381,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK11(X0,X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X3,X2)
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,sK11(X0,X1,X2)),X1)
      | ~ m1_subset_1(sK7(X0,X2,X3,sK11(X0,X1,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f380,f72])).

fof(f380,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK11(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,sK11(X0,X1,X2),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X3,X2)
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,sK11(X0,X1,X2)),X1)
      | ~ m1_subset_1(sK7(X0,X2,X3,sK11(X0,X1,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK11(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,sK11(X0,X1,X2),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X3,X2)
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,sK11(X0,X1,X2)),X1)
      | ~ m1_subset_1(sK7(X0,X2,X3,sK11(X0,X1,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | sP0(X0,X3,X2)
      | ~ r1_orders_2(X0,sK11(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,sK11(X0,X1,X2),X2)
      | ~ m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f225,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f225,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X7)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6) ) ),
    inference(subsumption_resolution,[],[f222,f70])).

fof(f222,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X7)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X8)
      | ~ m1_subset_1(sK11(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X7)
      | ~ r1_orders_2(X6,sK11(X6,X9,X10),X8)
      | ~ m1_subset_1(sK11(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK7(X6,X8,X7,sK11(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6)
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f69,f73])).

fof(f73,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK11(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2208,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ sP0(sK1,sK2,sK3)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2207,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2207,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK2,sK3)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2206,f116])).

fof(f116,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl12_3
  <=> r1_orders_2(sK1,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f2206,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK2,sK3)
    | ~ spl12_2
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2205,f118])).

fof(f118,plain,
    ( r1_orders_2(sK1,sK4,sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl12_2
  <=> r1_orders_2(sK1,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f2205,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK2,sK3)
    | ~ spl12_8 ),
    inference(duplicate_literal_removal,[],[f2187])).

fof(f2187,plain,
    ( sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | sK4 = k11_lattice3(sK1,sK3,sK2)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK2,sK3)
    | ~ spl12_8 ),
    inference(resolution,[],[f2089,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
                & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
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
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f33])).

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
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f2089,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK6(sK1,sK2,sK3,X0),sK4)
        | k11_lattice3(sK1,sK3,sK2) = X0
        | ~ r1_orders_2(sK1,X0,sK2)
        | ~ r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f2088,f1790])).

fof(f2088,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK6(sK1,sK2,sK3,X0),sK4)
        | k11_lattice3(sK1,sK3,sK2) = X0
        | ~ r1_orders_2(sK1,X0,sK2)
        | ~ r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK2,sK3) )
    | ~ spl12_8 ),
    inference(duplicate_literal_removal,[],[f2087])).

fof(f2087,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK6(sK1,sK2,sK3,X0),sK4)
        | k11_lattice3(sK1,sK3,sK2) = X0
        | ~ r1_orders_2(sK1,X0,sK2)
        | ~ r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK2,sK3)
        | k11_lattice3(sK1,sK3,sK2) = X0
        | ~ r1_orders_2(sK1,X0,sK2)
        | ~ r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK2,sK3) )
    | ~ spl12_8 ),
    inference(resolution,[],[f2031,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2031,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK1,sK6(sK1,X6,sK3,X7),sK2)
        | r1_orders_2(sK1,sK6(sK1,X6,sK3,X7),sK4)
        | k11_lattice3(sK1,sK3,X6) = X7
        | ~ r1_orders_2(sK1,X7,X6)
        | ~ r1_orders_2(sK1,X7,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ sP0(sK1,X6,sK3) )
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f1996,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1996,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK6(sK1,X6,sK3,X7),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK1,X6,sK3,X7),sK2)
        | r1_orders_2(sK1,sK6(sK1,X6,sK3,X7),sK4)
        | k11_lattice3(sK1,sK3,X6) = X7
        | ~ r1_orders_2(sK1,X7,X6)
        | ~ r1_orders_2(sK1,X7,sK3)
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ sP0(sK1,X6,sK3) )
    | ~ spl12_8 ),
    inference(resolution,[],[f114,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK1,X5,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X5,sK2)
        | r1_orders_2(sK1,X5,sK4) )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl12_8
  <=> ! [X5] :
        ( r1_orders_2(sK1,X5,sK4)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X5,sK2)
        | ~ r1_orders_2(sK1,X5,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(f1942,plain,
    ( ~ spl12_1
    | spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7 ),
    inference(avatar_contradiction_clause,[],[f1941])).

fof(f1941,plain,
    ( $false
    | ~ spl12_1
    | spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f1940,f105])).

fof(f105,plain,
    ( r1_orders_2(sK1,sK5,sK2)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl12_6
  <=> r1_orders_2(sK1,sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f1940,plain,
    ( ~ r1_orders_2(sK1,sK5,sK2)
    | ~ spl12_1
    | spl12_4
    | ~ spl12_5
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f1939,f109])).

fof(f109,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl12_7
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f1939,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK5,sK2)
    | ~ spl12_1
    | spl12_4
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f1925,f97])).

fof(f97,plain,
    ( ~ r1_orders_2(sK1,sK5,sK4)
    | spl12_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl12_4
  <=> r1_orders_2(sK1,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f1925,plain,
    ( r1_orders_2(sK1,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK5,sK2)
    | ~ spl12_1
    | ~ spl12_5 ),
    inference(resolution,[],[f1877,f101])).

fof(f101,plain,
    ( r1_orders_2(sK1,sK5,sK3)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl12_5
  <=> r1_orders_2(sK1,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f1877,plain,
    ( ! [X16] :
        ( ~ r1_orders_2(sK1,X16,sK3)
        | r1_orders_2(sK1,X16,sK4)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1876,f46])).

fof(f1876,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1875,f47])).

fof(f1875,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ v2_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1874,f48])).

fof(f1874,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1873,f50])).

fof(f1873,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1872,f49])).

fof(f1872,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f625,f1790])).

fof(f625,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,X16,sK4)
        | ~ r1_orders_2(sK1,X16,sK3)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X16,sK2)
        | ~ sP0(sK1,sK2,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl12_1 ),
    inference(superposition,[],[f333,f111])).

fof(f111,plain,
    ( k12_lattice3(sK1,sK2,sK3) = sK4
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f333,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,k12_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,k12_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f177,f81])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,k12_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f176,f149])).

fof(f149,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(k12_lattice3(X6,X7,X8),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(k12_lattice3(X6,X7,X8),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(superposition,[],[f82,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,k12_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f83,f80])).

fof(f83,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k11_lattice3(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1900,plain,
    ( ~ spl12_1
    | spl12_3 ),
    inference(avatar_contradiction_clause,[],[f1899])).

fof(f1899,plain,
    ( $false
    | ~ spl12_1
    | spl12_3 ),
    inference(subsumption_resolution,[],[f94,f1898])).

fof(f1898,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1897,f46])).

fof(f1897,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1896,f47])).

fof(f1896,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1895,f48])).

fof(f1895,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1894,f50])).

fof(f1894,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f1893,f49])).

fof(f1893,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f399,f1790])).

fof(f399,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(superposition,[],[f283,f111])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X2,X1),X1)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f281,f149])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X2,X1),X1)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X2,X1),X1)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f146,f81])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f85,f80])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1801,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_contradiction_clause,[],[f1800])).

fof(f1800,plain,
    ( $false
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f1790,f417])).

fof(f417,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f416,f46])).

fof(f416,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f415,f47])).

fof(f415,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f414,f48])).

fof(f414,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f413,f50])).

fof(f413,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f412,f49])).

fof(f412,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f407,f91])).

fof(f91,plain,
    ( ~ r1_orders_2(sK1,sK4,sK2)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f407,plain,
    ( r1_orders_2(sK1,sK4,sK2)
    | ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl12_1 ),
    inference(superposition,[],[f298,f111])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X2,X1),X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f296,f149])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X2,X1),X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X2,X1),X2)
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f147,f81])).

fof(f147,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k12_lattice3(X3,X4,X5),u1_struct_0(X3))
      | r1_orders_2(X3,k12_lattice3(X3,X4,X5),X5)
      | ~ sP0(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f84,f80])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f52,f90,f87])).

fof(f52,plain,
    ( r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f117,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f53,f93,f87])).

fof(f53,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | k12_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,
    ( spl12_1
    | spl12_8 ),
    inference(avatar_split_clause,[],[f54,f113,f87])).

fof(f54,plain,(
    ! [X5] :
      ( r1_orders_2(sK1,X5,sK4)
      | ~ r1_orders_2(sK1,X5,sK3)
      | ~ r1_orders_2(sK1,X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | k12_lattice3(sK1,sK2,sK3) = sK4 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_7 ),
    inference(avatar_split_clause,[],[f55,f108,f93,f90,f87])).

fof(f55,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_6 ),
    inference(avatar_split_clause,[],[f56,f104,f93,f90,f87])).

fof(f56,plain,
    ( r1_orders_2(sK1,sK5,sK2)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_5 ),
    inference(avatar_split_clause,[],[f57,f100,f93,f90,f87])).

fof(f57,plain,
    ( r1_orders_2(sK1,sK5,sK3)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f58,f96,f93,f90,f87])).

fof(f58,plain,
    ( ~ r1_orders_2(sK1,sK5,sK4)
    | ~ r1_orders_2(sK1,sK4,sK3)
    | ~ r1_orders_2(sK1,sK4,sK2)
    | k12_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
