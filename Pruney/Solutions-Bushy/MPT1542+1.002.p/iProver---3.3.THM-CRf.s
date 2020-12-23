%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1542+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:50 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_14780)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
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
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
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
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
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
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
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
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
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
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v1_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f13,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK10))
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK9,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v1_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(sK8,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            & m1_subset_1(X1,u1_struct_0(sK8)) )
        | ~ v1_lattice3(sK8) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(sK8,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
        | v1_lattice3(sK8) )
      & l1_orders_2(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
        & m1_subset_1(sK10,u1_struct_0(sK8))
        & m1_subset_1(sK9,u1_struct_0(sK8)) )
      | ~ v1_lattice3(sK8) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r1_yellow_0(sK8,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
      | v1_lattice3(sK8) )
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
                      ( r1_orders_2(X0,X3,X4)
                      | ~ r1_orders_2(X0,X2,X4)
                      | ~ r1_orders_2(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3)
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
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
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
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( r1_orders_2(X0,X7,X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f26,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK6(X0,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X5,X6))
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
        & r1_orders_2(X0,X2,sK5(X0,X3))
        & r1_orders_2(X0,X1,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK4(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK3(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
                & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
                & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK4(X0),X3)
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0),u1_struct_0(X0))
          & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK6(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK6(X0,X5,X6))
                  & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f26,f25,f24,f23])).

fof(f45,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X3] :
      ( r1_yellow_0(sK8,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | ~ m1_subset_1(X3,u1_struct_0(sK8))
      | v1_lattice3(sK8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
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
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
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

fof(f48,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK3(X0),sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK4(X0),sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | ~ r1_orders_2(X0,X3,sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK6(X0,X5,X6))
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
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

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

cnf(c_856,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_479])).

cnf(c_857,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_7097,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_857])).

cnf(c_7637,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7097])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7115,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | ~ r1_orders_2(X0_48,X2_49,X1_49)
    | r1_orders_2(X0_48,sK6(X0_48,X2_49,X0_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X2_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7619,plain,
    ( r1_orders_2(X0_48,X0_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,X2_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,sK6(X0_48,X2_49,X0_49),X1_49) = iProver_top
    | m1_subset_1(X2_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | sP0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7115])).

cnf(c_14,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_881,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_479])).

cnf(c_882,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_7096,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | ~ r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_882])).

cnf(c_7638,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7096])).

cnf(c_9213,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7619,c_7638])).

cnf(c_13685,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_7115,c_7096])).

cnf(c_9264,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9213])).

cnf(c_6,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7117,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7617,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48)) = iProver_top
    | sP0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7117])).

cnf(c_29,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_351,plain,
    ( ~ l1_orders_2(X0)
    | sP0(X0)
    | ~ v1_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_12,c_1])).

cnf(c_533,plain,
    ( sP0(X0)
    | ~ v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_30])).

cnf(c_534,plain,
    ( sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_2781,plain,
    ( sP0(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_534])).

cnf(c_2836,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_29,c_2781])).

cnf(c_7104,negated_conjecture,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2836])).

cnf(c_7630,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7104])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_23,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_437,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_438,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30])).

cnf(c_443,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X2),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_569,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0,X2),X1)
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_443])).

cnf(c_7108,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X2_49),X1_49)
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_7626,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X2_49),X1_49) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7108])).

cnf(c_25,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_387,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_388,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_30])).

cnf(c_393,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_568,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X0,X1))
    | ~ r1_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_393])).

cnf(c_7109,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_568])).

cnf(c_7625,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7109])).

cnf(c_19,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X0,sK7(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_750,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK7(X1,X3,X0,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_479])).

cnf(c_751,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X2,sK7(X2,X0,sK8,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_7101,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X2_49,sK7(X2_49,X0_49,sK8,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_49,X2_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_751])).

cnf(c_7633,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,sK7(X1_49,X0_49,sK8,X2_49)) = iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7101])).

cnf(c_18,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X3,sK7(X0,X1,X2,X3))
    | k10_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_775,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK7(X1,X3,X0,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | k10_lattice3(X0,X3,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_479])).

cnf(c_776,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | ~ r1_orders_2(sK8,X1,sK7(X2,X0,sK8,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_7100,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | ~ r1_orders_2(sK8,X1_49,sK7(X2_49,X0_49,sK8,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | k10_lattice3(sK8,X0_49,X2_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_776])).

cnf(c_7634,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X2_49,sK7(X1_49,X0_49,sK8,X2_49)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7100])).

cnf(c_8770,plain,
    ( k10_lattice3(sK8,X0_49,X1_49) = X1_49
    | r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X1_49,X1_49) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7633,c_7634])).

cnf(c_9429,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7625,c_8770])).

cnf(c_7111,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_7161,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7111])).

cnf(c_9991,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9429,c_7161])).

cnf(c_9992,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,X1_49),k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9991])).

cnf(c_10002,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7626,c_9992])).

cnf(c_7167,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7109])).

cnf(c_10182,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10002,c_7161,c_7167])).

cnf(c_10183,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10182])).

cnf(c_24,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_414,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_415,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_30])).

cnf(c_418,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_567,plain,
    ( r1_orders_2(sK8,X0,k10_lattice3(sK8,X1,X0))
    | ~ r1_yellow_0(sK8,k2_tarski(X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_418])).

cnf(c_7110,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_567])).

cnf(c_7624,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7110])).

cnf(c_10193,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10183,c_7624])).

cnf(c_10197,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49)) = k10_lattice3(sK8,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7630,c_10193])).

cnf(c_10666,plain,
    ( k10_lattice3(sK8,X0_49,k10_lattice3(sK8,X0_49,sK4(sK8))) = k10_lattice3(sK8,X0_49,sK4(sK8))
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7617,c_10197])).

cnf(c_10935,plain,
    ( k10_lattice3(sK8,sK4(sK8),k10_lattice3(sK8,sK4(sK8),sK4(sK8))) = k10_lattice3(sK8,sK4(sK8),sK4(sK8))
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7617,c_10666])).

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

cnf(c_8001,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7111])).

cnf(c_8174,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8001])).

cnf(c_8175,plain,
    ( m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8174])).

cnf(c_8155,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,X0_49,sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,sK4(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7110])).

cnf(c_8592,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8155])).

cnf(c_8594,plain,
    ( r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8592])).

cnf(c_8140,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7104])).

cnf(c_8593,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8140])).

cnf(c_8596,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8593])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7118,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | m1_subset_1(sK5(X0_48,X0_49),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_9030,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7118])).

cnf(c_9031,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9030])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | r1_orders_2(X0,sK3(X0),sK5(X0,X1))
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7119,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | r1_orders_2(X0_48,sK3(X0_48),sK5(X0_48,X0_49))
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9029,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7119])).

cnf(c_9033,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9029])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | r1_orders_2(X0,sK4(X0),sK5(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7120,plain,
    ( ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | r1_orders_2(X0_48,sK4(X0_48),sK5(X0_48,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9028,plain,
    ( ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7120])).

cnf(c_9035,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9028])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,sK5(X0,X1))
    | ~ r1_orders_2(X0,sK3(X0),X1)
    | ~ r1_orders_2(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7121,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK5(X0_48,X0_49))
    | ~ r1_orders_2(X0_48,sK3(X0_48),X0_49)
    | ~ r1_orders_2(X0_48,sK4(X0_48),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_9027,plain,
    ( ~ r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7121])).

cnf(c_9037,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,sK3(sK8),sK4(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9027])).

cnf(c_8139,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),X0_49))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7109])).

cnf(c_9202,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8)))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8139])).

cnf(c_9203,plain,
    ( r1_orders_2(sK8,sK3(sK8),k10_lattice3(sK8,sK3(sK8),sK4(sK8))) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9202])).

cnf(c_11451,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | r1_orders_2(sK8,k10_lattice3(sK8,X0_49,sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,sK4(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7108])).

cnf(c_12375,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))))
    | ~ r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8)))
    | ~ m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_11451])).

cnf(c_12376,plain,
    ( r1_orders_2(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) = iProver_top
    | r1_orders_2(sK8,sK3(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_orders_2(sK8,sK4(sK8),sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8)))) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(sK3(sK8),sK4(sK8))) != iProver_top
    | m1_subset_1(sK5(sK8,k10_lattice3(sK8,sK3(sK8),sK4(sK8))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12375])).

cnf(c_12386,plain,
    ( sP0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10935,c_88,c_91,c_8175,c_8594,c_8596,c_9031,c_9033,c_9035,c_9037,c_9203,c_12376])).

cnf(c_12388,plain,
    ( sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12386])).

cnf(c_13732,plain,
    ( ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13685,c_9264,c_12388])).

cnf(c_13733,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_13732])).

cnf(c_17,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_yellow_0(X2,k2_tarski(X1,X0))
    | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_802,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | m1_subset_1(sK7(X1,X3,X0,X2),u1_struct_0(X0))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_479])).

cnf(c_803,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X0,sK8,X1),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_7099,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2_49,X0_49,sK8,X1_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_803])).

cnf(c_13749,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13733,c_7099])).

cnf(c_13750,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13749])).

cnf(c_14540,plain,
    ( m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9213,c_13750])).

cnf(c_14541,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X3_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X3_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X3_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14540])).

cnf(c_14554,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X0_49,X1_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,sK6(sK8,X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7637,c_14541])).

cnf(c_14920,plain,
    ( r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7637,c_14554])).

cnf(c_16,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X0,X3)
    | ~ r1_orders_2(X2,X1,X3)
    | r1_orders_2(X2,X1,sK7(X0,X1,X2,X3))
    | r1_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_829,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK7(X1,X3,X0,X2))
    | r1_yellow_0(X0,k2_tarski(X3,X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X6 != X2
    | X4 != X3
    | X5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_479])).

cnf(c_830,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,X0,sK7(X2,X0,sK8,X1))
    | r1_yellow_0(sK8,k2_tarski(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_7098,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X2_49,X1_49)
    | r1_orders_2(sK8,X0_49,sK7(X2_49,X0_49,sK8,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_830])).

cnf(c_7636,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,sK7(X2_49,X0_49,sK8,X1_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7098])).

cnf(c_8686,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X3_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7626,c_7638])).

cnf(c_8904,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X3_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_49,X3_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_7096,c_7108])).

cnf(c_10044,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49)))
    | ~ r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X3_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8904,c_7111,c_7099])).

cnf(c_10045,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10044])).

cnf(c_12882,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X3_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X3_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X3_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8686,c_10045])).

cnf(c_12896,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X1_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7637,c_12882])).

cnf(c_7623,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7111])).

cnf(c_14242,plain,
    ( r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X1_49,X0_49))) != iProver_top
    | r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12896,c_7623,c_7625])).

cnf(c_14245,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7636,c_14242])).

cnf(c_7164,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) = iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7110])).

cnf(c_10083,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X2_49)))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X2_49))
    | ~ r1_orders_2(sK8,X2_49,k10_lattice3(sK8,X0_49,X2_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_49,X2_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10044,c_7098])).

cnf(c_10830,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,k10_lattice3(sK8,X0_49,X2_49)))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X2_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X2_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10083,c_7111,c_7110])).

cnf(c_10856,plain,
    ( ~ r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X0_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10830,c_7097])).

cnf(c_10867,plain,
    ( ~ r1_orders_2(sK8,X1_49,k10_lattice3(sK8,X0_49,X1_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10856,c_7109])).

cnf(c_10868,plain,
    ( ~ r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_10867])).

cnf(c_10869,plain,
    ( r1_orders_2(sK8,X0_49,k10_lattice3(sK8,X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10868])).

cnf(c_14713,plain,
    ( r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14245,c_7164,c_10869])).

cnf(c_14714,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14713])).

cnf(c_14022,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X2_49,X0_49)))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X2_49,X0_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X2_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_13749,c_7098])).

cnf(c_14480,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14022,c_7097])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7113,plain,
    ( r1_orders_2(X0_48,X0_49,sK6(X0_48,X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_8282,plain,
    ( r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7113])).

cnf(c_14743,plain,
    ( ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14480,c_8282,c_12388])).

cnf(c_14744,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_14743])).

cnf(c_10871,plain,
    ( ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10868,c_7111,c_7110])).

cnf(c_10872,plain,
    ( ~ r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_10871])).

cnf(c_14018,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK7(X1_49,X2_49,sK8,sK6(sK8,X1_49,X0_49)))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X1_49,X0_49))
    | ~ r1_orders_2(sK8,X2_49,sK6(sK8,X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_13749,c_7097])).

cnf(c_14058,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X0_49,X1_49))
    | ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14018,c_7098])).

cnf(c_14420,plain,
    ( ~ r1_orders_2(sK8,X1_49,sK6(sK8,X0_49,X1_49))
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14058,c_8282,c_12388])).

cnf(c_14421,plain,
    ( ~ r1_orders_2(sK8,X0_49,sK6(sK8,X1_49,X0_49))
    | r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_14420])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7114,plain,
    ( r1_orders_2(X0_48,X0_49,sK6(X0_48,X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_14456,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_14421,c_7114])).

cnf(c_14747,plain,
    ( r1_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14744,c_10872,c_12388,c_14456])).

cnf(c_14748,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_14747])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7112,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | m1_subset_1(sK6(X0_48,X1_49,X0_49),u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_14773,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_14748,c_7112])).

cnf(c_14774,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14773])).

cnf(c_15035,plain,
    ( m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | r1_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14920,c_7161,c_14714,c_14780])).

cnf(c_15036,plain,
    ( r1_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15035])).

cnf(c_26,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_0,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_365,plain,
    ( ~ l1_orders_2(X0)
    | ~ sP0(X0)
    | v1_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_12,c_0])).

cnf(c_523,plain,
    ( ~ sP0(X0)
    | v1_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_30])).

cnf(c_524,plain,
    ( ~ sP0(sK8)
    | v1_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_2783,plain,
    ( ~ sP0(sK8)
    | v1_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_524])).

cnf(c_2833,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_26,c_2783])).

cnf(c_7105,negated_conjecture,
    ( ~ r1_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2833])).

cnf(c_7629,plain,
    ( r1_yellow_0(sK8,k2_tarski(sK9,sK10)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7105])).

cnf(c_15042,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15036,c_7629])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_lattice3(sK8) ),
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
    | ~ v1_lattice3(sK8) ),
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
    inference(minisat,[status(thm)],[c_15042,c_12386,c_589,c_580])).


%------------------------------------------------------------------------------
