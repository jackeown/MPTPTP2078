%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1543+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:50 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  266 (5861 expanded)
%              Number of clauses        :  194 (1539 expanded)
%              Number of leaves         :   15 (1492 expanded)
%              Depth                    :   38
%              Number of atoms          : 1585 (47885 expanded)
%              Number of equality atoms :  342 (2198 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X5,X2)
                                & r1_orders_2(X0,X5,X1) )
                             => r1_orders_2(X0,X5,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f12,f18])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v2_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f13,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(X1,sK10))
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK9,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v2_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            & m1_subset_1(X1,u1_struct_0(sK8)) )
        | ~ v2_lattice3(sK8) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(sK8,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
        | v2_lattice3(sK8) )
      & l1_orders_2(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
        & m1_subset_1(sK10,u1_struct_0(sK8))
        & m1_subset_1(sK9,u1_struct_0(sK8)) )
      | ~ v2_lattice3(sK8) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r2_yellow_0(sK8,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
      | v2_lattice3(sK8) )
    & l1_orders_2(sK8)
    & v5_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f35,f38,f37,f36])).

fof(f66,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,plain,(
    ! [X0] :
      ( sP0(X0)
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
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f26,plain,(
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
            ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK6(X0,X5,X6),X6)
        & r1_orders_2(X0,sK6(X0,X5,X6),X5)
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
        & r1_orders_2(X0,sK5(X0,X3),X2)
        & r1_orders_2(X0,sK5(X0,X3),X1)
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
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
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK4(X0))
                & r1_orders_2(X0,X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK4(X0))
            | ~ r1_orders_2(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
                    & r1_orders_2(X0,X4,sK3(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK3(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
                & r1_orders_2(X0,sK5(X0,X3),sK4(X0))
                & r1_orders_2(X0,sK5(X0,X3),sK3(X0))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,sK4(X0))
              | ~ r1_orders_2(X0,X3,sK3(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0),u1_struct_0(X0))
          & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
                      | ~ r1_orders_2(X0,X8,X6)
                      | ~ r1_orders_2(X0,X8,X5)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,sK6(X0,X5,X6),X6)
                  & r1_orders_2(X0,sK6(X0,X5,X6),X5)
                  & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f26,f25,f24,f23])).

fof(f45,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X3] :
      ( r2_yellow_0(sK8,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | ~ m1_subset_1(X3,u1_struct_0(sK8))
      | v2_lattice3(sK8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f16,f15])).

fof(f52,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_orders_2(X0,X4,X2)
      | ~ r1_orders_2(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X4,X2)
      | ~ r1_orders_2(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f46,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK4(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK3(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | ~ r1_orders_2(X0,sK5(X0,X3),X3)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_473,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_474,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | sP2(X0,X1,sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_30])).

cnf(c_479,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_478])).

cnf(c_829,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X3)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_479])).

cnf(c_830,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X1)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_7049,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_830])).

cnf(c_7587,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X1_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7049])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK6(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7066,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | ~ r1_orders_2(X0_48,X0_49,X2_49)
    | r1_orders_2(X0_48,X0_49,sK6(X0_48,X2_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X2_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7570,plain,
    ( r1_orders_2(X0_48,X0_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,X0_49,X2_49) != iProver_top
    | r1_orders_2(X0_48,X0_49,sK6(X0_48,X2_49,X1_49)) = iProver_top
    | m1_subset_1(X2_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | sP0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7066])).

cnf(c_14,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_881,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X2,X3,X0,X1),X1)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_479])).

cnf(c_882,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X0)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_7047,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | ~ r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_882])).

cnf(c_7589,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7047])).

cnf(c_9110,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7570,c_7589])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_7062,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_7574,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7062])).

cnf(c_6,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7068,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7568,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48)) = iProver_top
    | sP0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7068])).

cnf(c_29,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_351,plain,
    ( ~ l1_orders_2(X0)
    | sP0(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_12,c_1])).

cnf(c_533,plain,
    ( sP0(X0)
    | ~ v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_30])).

cnf(c_534,plain,
    ( sP0(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_2765,plain,
    ( sP0(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_534])).

cnf(c_2819,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_29,c_2765])).

cnf(c_7055,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2819])).

cnf(c_7581,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7055])).

cnf(c_23,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_437,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_438,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30])).

cnf(c_443,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_569,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_443])).

cnf(c_7059,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,X0_49,k11_lattice3(sK8,X1_49,X2_49))
    | ~ r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_7577,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X0_49,k11_lattice3(sK8,X1_49,X2_49)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7059])).

cnf(c_25,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_387,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_388,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_30])).

cnf(c_393,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_568,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_393])).

cnf(c_7060,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_568])).

cnf(c_7576,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7060])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_723,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X3)
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_479])).

cnf(c_724,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_7053,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_49,X2_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_724])).

cnf(c_7583,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,sK7(X1_49,X0_49,sK8,X2_49),X0_49) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7053])).

cnf(c_18,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_775,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X2,X3,X0,X1),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_479])).

cnf(c_776,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_7051,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | ~ r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_49,X2_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_776])).

cnf(c_7585,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,sK7(X1_49,X0_49,sK8,X2_49),X2_49) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7051])).

cnf(c_8570,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X0_49
    | r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X0_49) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7583,c_7585])).

cnf(c_9303,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7576,c_8570])).

cnf(c_7112,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7062])).

cnf(c_10248,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9303,c_7112])).

cnf(c_10249,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10248])).

cnf(c_10259,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7577,c_10249])).

cnf(c_24,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_414,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_415,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_30])).

cnf(c_418,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_567,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_418])).

cnf(c_7061,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_567])).

cnf(c_7115,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7061])).

cnf(c_7118,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7060])).

cnf(c_10855,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10259,c_7112,c_7115,c_7118])).

cnf(c_10856,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10855])).

cnf(c_10865,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7581,c_10856])).

cnf(c_11067,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,sK4(sK8)),X0_49) = k11_lattice3(sK8,X0_49,sK4(sK8))
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7568,c_10865])).

cnf(c_11428,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),sK4(sK8)),k11_lattice3(sK8,X0_49,X1_49)) = k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),sK4(sK8))
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7574,c_11067])).

cnf(c_7,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_86,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_88,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_89,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_91,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_7977,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7062])).

cnf(c_8144,plain,
    ( m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7977])).

cnf(c_8145,plain,
    ( m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8144])).

cnf(c_7952,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,sK3(sK8)),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7061])).

cnf(c_8214,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7952])).

cnf(c_8215,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8214])).

cnf(c_7953,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,sK3(sK8)),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7060])).

cnf(c_8228,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7953])).

cnf(c_8229,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8228])).

cnf(c_7955,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7055])).

cnf(c_8473,plain,
    ( r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7955])).

cnf(c_8474,plain,
    ( r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8473])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | r1_orders_2(X0,sK5(X0,X1),sK4(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7071,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | r1_orders_2(X0_48,sK5(X0_48,X0_49),sK4(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_8698,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7071])).

cnf(c_9284,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8698])).

cnf(c_9285,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8)) = iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9284])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | r1_orders_2(X0,sK5(X0,X1),sK3(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7070,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | r1_orders_2(X0_48,sK5(X0_48,X0_49),sK3(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_8699,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),sK3(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7070])).

cnf(c_9291,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8699])).

cnf(c_9292,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8)) = iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9291])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7069,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | m1_subset_1(sK5(X0_48,X0_49),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_8700,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7069])).

cnf(c_9818,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8700])).

cnf(c_9819,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9818])).

cnf(c_10179,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),X0_49)
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,X0_49,sK3(sK8)))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7059])).

cnf(c_11760,plain,
    ( r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8)))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_10179])).

cnf(c_11762,plain,
    ( r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8))) = iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11760])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | ~ r1_orders_2(X0,sK5(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7072,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | ~ r1_orders_2(X0_48,sK5(X0_48,X0_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_11761,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7072])).

cnf(c_11764,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11761])).

cnf(c_11767,plain,
    ( sP0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11428,c_88,c_91,c_8145,c_8215,c_8229,c_8474,c_9285,c_9292,c_9819,c_11762,c_11764])).

cnf(c_13643,plain,
    ( m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9110,c_88,c_91,c_8145,c_8215,c_8229,c_8474,c_9285,c_9292,c_9819,c_11762,c_11764])).

cnf(c_13644,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13643])).

cnf(c_17,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r2_yellow_0(X2,k2_tarski(X1,X0))
    | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_802,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X3,X0,X1),u1_struct_0(X0))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_479])).

cnf(c_803,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X1,sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_7050,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2_49,X1_49,sK8,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_803])).

cnf(c_7586,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X2_49,X1_49,sK8,X0_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7050])).

cnf(c_13660,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13644,c_7586])).

cnf(c_13665,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X1_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X1_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X1_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7587,c_13660])).

cnf(c_8888,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_7047,c_7059])).

cnf(c_10302,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8888,c_7062,c_7050])).

cnf(c_10341,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X1_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10302,c_7049])).

cnf(c_10879,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X1_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10341,c_7062,c_7061])).

cnf(c_15,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_856,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X2)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X1
    | X4 != X3
    | X5 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_479])).

cnf(c_857,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X2)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_7048,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X2_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_857])).

cnf(c_10905,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10879,c_7048])).

cnf(c_7860,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7574])).

cnf(c_10916,plain,
    ( ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10905,c_7061,c_7060,c_7860])).

cnf(c_10917,plain,
    ( ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_10916])).

cnf(c_10918,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10917])).

cnf(c_13553,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_7066,c_7047])).

cnf(c_13661,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13660])).

cnf(c_13857,plain,
    ( ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13553,c_13661])).

cnf(c_13858,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_13857])).

cnf(c_14068,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X1_49,X2_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X1_49,X2_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X1_49,X2_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X2_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_13858,c_7049])).

cnf(c_14368,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0_49,X0_49),X0_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X0_49,X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14068,c_7049])).

cnf(c_11769,plain,
    ( sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11767])).

cnf(c_14364,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14068,c_7048])).

cnf(c_9,plain,
    ( r1_orders_2(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7065,plain,
    ( r1_orders_2(X0_48,sK6(X0_48,X0_49,X1_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_7571,plain,
    ( r1_orders_2(X0_48,sK6(X0_48,X0_49,X1_49),X1_49) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | sP0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7065])).

cnf(c_7588,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X2_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7048])).

cnf(c_13664,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X0_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X0_49),X0_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X0_49),X1_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7588,c_13660])).

cnf(c_14190,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X1_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7587,c_13664])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7064,plain,
    ( r1_orders_2(X0_48,sK6(X0_48,X0_49,X1_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_8316,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7064])).

cnf(c_8326,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8316])).

cnf(c_14410,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X1_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14190,c_88,c_91,c_8145,c_8215,c_8229,c_8326,c_8474,c_9285,c_9292,c_9819,c_11762,c_11764])).

cnf(c_14421,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_14410])).

cnf(c_14481,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14421])).

cnf(c_14483,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14364,c_11769,c_14481])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7063,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | m1_subset_1(sK6(X0_48,X1_49,X0_49),u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_14509,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_14483,c_7063])).

cnf(c_14514,plain,
    ( ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14368,c_11769,c_14509])).

cnf(c_14515,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_14514])).

cnf(c_14516,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14515])).

cnf(c_14561,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13665,c_10918,c_14516])).

cnf(c_14562,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14561])).

cnf(c_26,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_0,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_365,plain,
    ( ~ l1_orders_2(X0)
    | ~ sP0(X0)
    | v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_12,c_0])).

cnf(c_523,plain,
    ( ~ sP0(X0)
    | v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_30])).

cnf(c_524,plain,
    ( ~ sP0(sK8)
    | v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_2767,plain,
    ( ~ sP0(sK8)
    | v2_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_524])).

cnf(c_2816,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_26,c_2767])).

cnf(c_7056,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2816])).

cnf(c_7580,plain,
    ( r2_yellow_0(sK8,k2_tarski(sK9,sK10)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7056])).

cnf(c_14568,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_14562,c_7580])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_588,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_524,c_27])).

cnf(c_589,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_579,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_524,c_28])).

cnf(c_580,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14568,c_11767,c_589,c_580])).


%------------------------------------------------------------------------------
