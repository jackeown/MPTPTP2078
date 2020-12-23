%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1559+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:53 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :  249 (2641 expanded)
%              Number of clauses        :  180 ( 892 expanded)
%              Number of leaves         :   16 ( 609 expanded)
%              Depth                    :   43
%              Number of atoms          : 1283 (16964 expanded)
%              Number of equality atoms :  279 (2636 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
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
      | ~ sP0(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
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
      | ~ sP0(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f33,plain,(
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
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK1(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK1(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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

fof(f13,plain,(
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
    inference(rectify,[],[f6])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP0(X2,X1,X0,X3)
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
    inference(definition_folding,[],[f21,f30])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP0(X2,X1,X0,X3)
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
    inference(rectify,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
         => k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) = k2_yellow_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
              & r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1) )
           => k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) = k2_yellow_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) != k2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) != k2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) != k2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
     => ( k11_lattice3(X0,k2_yellow_0(X0,sK4),k2_yellow_0(X0,sK5)) != k2_yellow_0(X0,k2_xboole_0(sK4,sK5))
        & r2_yellow_0(X0,k2_xboole_0(sK4,sK5))
        & r2_yellow_0(X0,sK5)
        & r2_yellow_0(X0,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) != k2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( k11_lattice3(sK3,k2_yellow_0(sK3,X1),k2_yellow_0(sK3,X2)) != k2_yellow_0(sK3,k2_xboole_0(X1,X2))
          & r2_yellow_0(sK3,k2_xboole_0(X1,X2))
          & r2_yellow_0(sK3,X2)
          & r2_yellow_0(sK3,X1) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) != k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    & r2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    & r2_yellow_0(sK3,sK5)
    & r2_yellow_0(sK3,sK4)
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f40,f39])).

fof(f73,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,sK1(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X0))
         => ( ( ( r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
             => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
            & ( ( r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) )
             => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f37])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f75,plain,(
    r2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) != k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    r2_yellow_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_704,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_705,plain,
    ( sP0(X0,X1,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | sP0(X0,X1,sK3,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_34])).

cnf(c_710,plain,
    ( sP0(X0,X1,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_958,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X2,X3,X0,X1),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_710])).

cnf(c_959,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ r1_orders_2(sK3,sK1(X1,X2,sK3,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_1335,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | ~ r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_49,X1_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_959])).

cnf(c_2226,plain,
    ( ~ r1_orders_2(sK3,sK1(X0_49,k2_yellow_0(sK3,X0_50),sK3,k2_yellow_0(sK3,X1_50)),k2_yellow_0(sK3,X1_50))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,X1_50),X0_49)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,X1_50),k2_yellow_0(sK3,X0_50))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,X0_50),X0_49) = k2_yellow_0(sK3,X1_50) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_39355,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK1(X0,X1,X2,X3),X0)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_933,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X2,X3,X0,X1),X2)
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_710])).

cnf(c_934,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK1(X1,X2,sK3,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_1336,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_49,X1_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_934])).

cnf(c_2144,plain,
    ( r1_orders_2(sK3,sK1(X0_49,k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),X0_49)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),X0_49) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_3099,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,X0_50))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,X0_50))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,X0_50)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_19745,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_28,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_400,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_401,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_lattice3(sK3,X2,X1)
    | r1_lattice3(sK3,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattice3(sK3,X2,X0)
    | ~ r1_lattice3(sK3,X2,X1)
    | ~ r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_34])).

cnf(c_404,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_lattice3(sK3,X2,X1)
    | r1_lattice3(sK3,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_1354,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_lattice3(sK3,X0_50,X1_49)
    | r1_lattice3(sK3,X0_50,X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_3564,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,X1_50),sK3,k2_yellow_0(sK3,X2_50)),k2_yellow_0(sK3,X0_50))
    | r1_lattice3(sK3,X3_50,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,X1_50),sK3,k2_yellow_0(sK3,X2_50)))
    | ~ r1_lattice3(sK3,X3_50,k2_yellow_0(sK3,X0_50))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,X1_50),sK3,k2_yellow_0(sK3,X2_50)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_5076,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,X0_50))
    | r1_lattice3(sK3,X1_50,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,X1_50,k2_yellow_0(sK3,X0_50))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3564])).

cnf(c_12785,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK5))
    | r1_lattice3(sK3,X0_50,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,X0_50,k2_yellow_0(sK3,sK5))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5076])).

cnf(c_17882,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK5))
    | r1_lattice3(sK3,sK5,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12785])).

cnf(c_5,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,k2_xboole_0(X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_808,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,k2_xboole_0(X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_34])).

cnf(c_809,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ r1_lattice3(sK3,X2,X1)
    | r1_lattice3(sK3,k2_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_1345,plain,
    ( ~ r1_lattice3(sK3,X0_50,X0_49)
    | ~ r1_lattice3(sK3,X1_50,X0_49)
    | r1_lattice3(sK3,k2_xboole_0(X1_50,X0_50),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_2895,plain,
    ( ~ r1_lattice3(sK3,X0_50,sK1(k2_yellow_0(sK3,X1_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,X2_50,sK1(k2_yellow_0(sK3,X1_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | r1_lattice3(sK3,k2_xboole_0(X2_50,X0_50),sK1(k2_yellow_0(sK3,X1_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X1_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_17832,plain,
    ( r1_lattice3(sK3,k2_xboole_0(sK4,sK5),sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,sK5,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,sK4,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_906,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X2,X3,X0,X1),X3)
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_710])).

cnf(c_907,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK1(X1,X2,sK3,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_1337,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X2_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_49,X1_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_907])).

cnf(c_2143,plain,
    ( r1_orders_2(sK3,sK1(X0_49,k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK4))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),X0_49) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_2333,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK4))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,X0_50))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,X0_50)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_17564,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK4))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_3,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_826,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_34])).

cnf(c_827,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_24,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_447,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_448,plain,
    ( r1_orders_2(sK3,X0,k2_yellow_0(sK3,X1))
    | ~ r1_lattice3(sK3,X1,X0)
    | ~ r2_yellow_0(sK3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X1),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK3,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,X1)
    | ~ r1_lattice3(sK3,X1,X0)
    | r1_orders_2(sK3,X0,k2_yellow_0(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_34])).

cnf(c_453,plain,
    ( r1_orders_2(sK3,X0,k2_yellow_0(sK3,X1))
    | ~ r1_lattice3(sK3,X1,X0)
    | ~ r2_yellow_0(sK3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_452])).

cnf(c_860,plain,
    ( r1_orders_2(sK3,X0,k2_yellow_0(sK3,X1))
    | ~ r1_lattice3(sK3,X1,X0)
    | ~ r2_yellow_0(sK3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_827,c_453])).

cnf(c_1342,plain,
    ( r1_orders_2(sK3,X0_49,k2_yellow_0(sK3,X0_50))
    | ~ r1_lattice3(sK3,X0_50,X0_49)
    | ~ r2_yellow_0(sK3,X0_50)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_2893,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,X1_50))
    | ~ r1_lattice3(sK3,X1_50,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r2_yellow_0(sK3,X1_50)
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_5830,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r1_lattice3(sK3,k2_xboole_0(sK4,sK5),sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_12799,plain,
    ( r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r1_lattice3(sK3,k2_xboole_0(sK4,sK5),sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5830])).

cnf(c_5797,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,X1_50))
    | r1_lattice3(sK3,X2_50,sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,X2_50,k2_yellow_0(sK3,X1_50))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_12802,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,X0_50))
    | r1_lattice3(sK3,X1_50,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,X1_50,k2_yellow_0(sK3,X0_50))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5797])).

cnf(c_12809,plain,
    ( ~ r1_orders_2(sK3,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),k2_yellow_0(sK3,sK4))
    | r1_lattice3(sK3,sK4,sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))))
    | ~ r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12802])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1359,plain,
    ( k2_xboole_0(X0_50,X1_50) = k2_xboole_0(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_31,negated_conjecture,
    ( r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1357,negated_conjecture,
    ( r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1882,plain,
    ( r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_1344,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_827])).

cnf(c_1895,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_1897,plain,
    ( r1_orders_2(sK3,X0_49,k2_yellow_0(sK3,X0_50)) = iProver_top
    | r1_lattice3(sK3,X0_50,X0_49) != iProver_top
    | r2_yellow_0(sK3,X0_50) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1342])).

cnf(c_26,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
    | ~ r1_tarski(X2,X1)
    | ~ r2_yellow_0(X0,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_377,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
    | ~ r2_yellow_0(X0,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | X3 != X2
    | k2_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_378,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,k2_xboole_0(X1,X2)),k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ r2_yellow_0(X0,k2_xboole_0(X1,X2))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_793,plain,
    ( r1_orders_2(X0,k2_yellow_0(X0,k2_xboole_0(X1,X2)),k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ r2_yellow_0(X0,k2_xboole_0(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_34])).

cnf(c_794,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X0,X1)),k2_yellow_0(sK3,X0))
    | ~ r2_yellow_0(sK3,X0)
    | ~ r2_yellow_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_1346,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X0_50))
    | ~ r2_yellow_0(sK3,X0_50)
    | ~ r2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_794])).

cnf(c_1893,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X0_50)) = iProver_top
    | r2_yellow_0(sK3,X0_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_2305,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = iProver_top
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1893])).

cnf(c_1902,plain,
    ( k11_lattice3(sK3,X0_49,X1_49) = X2_49
    | r1_orders_2(sK3,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK3,sK1(X1_49,X0_49,sK3,X2_49),X0_49) = iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1337])).

cnf(c_1904,plain,
    ( k11_lattice3(sK3,X0_49,X1_49) = X2_49
    | r1_orders_2(sK3,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK3,sK1(X1_49,X0_49,sK3,X2_49),X2_49) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_3214,plain,
    ( k11_lattice3(sK3,X0_49,X1_49) = X0_49
    | r1_orders_2(sK3,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1904])).

cnf(c_4554,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))) != iProver_top
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_3214])).

cnf(c_4796,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50))) != iProver_top
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_4554])).

cnf(c_4805,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r1_lattice3(sK3,k2_xboole_0(X1_50,X0_50),k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50))) != iProver_top
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_4796])).

cnf(c_4913,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r1_lattice3(sK3,k2_xboole_0(X0_50,X1_50),k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))) != iProver_top
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_4805])).

cnf(c_25,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_198,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_3])).

cnf(c_199,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_429,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_35])).

cnf(c_430,plain,
    ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0))
    | ~ r2_yellow_0(sK3,X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( ~ r2_yellow_0(sK3,X0)
    | r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_34])).

cnf(c_435,plain,
    ( r1_lattice3(sK3,X0,k2_yellow_0(sK3,X0))
    | ~ r2_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_1353,plain,
    ( r1_lattice3(sK3,X0_50,k2_yellow_0(sK3,X0_50))
    | ~ r2_yellow_0(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1886,plain,
    ( r1_lattice3(sK3,X0_50,k2_yellow_0(sK3,X0_50)) = iProver_top
    | r2_yellow_0(sK3,X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_4910,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_4805])).

cnf(c_4990,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4913,c_4910])).

cnf(c_4994,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_4990])).

cnf(c_5009,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,X1_50),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_4994])).

cnf(c_6957,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50)),k2_yellow_0(sK3,X1_50)) = k2_yellow_0(sK3,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(sK3,X1_50) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(X1_50,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_5009])).

cnf(c_7033,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK5,sK4))
    | r2_yellow_0(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_6957])).

cnf(c_33,negated_conjecture,
    ( r2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( r2_yellow_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7192,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7033,c_40])).

cnf(c_7194,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_1359,c_7192])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_34])).

cnf(c_836,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_17,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_618,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_619,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X0)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_623,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_34])).

cnf(c_624,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X0)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_623])).

cnf(c_869,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X0)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_836,c_624])).

cnf(c_1340,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK3,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_869])).

cnf(c_1899,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0_49,X1_49),X0_49) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_7852,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7194,c_1899])).

cnf(c_1410,plain,
    ( m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_1412,plain,
    ( m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_2300,plain,
    ( m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_2301,plain,
    ( m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2300])).

cnf(c_9055,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7852,c_1412,c_2301])).

cnf(c_9059,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_9055])).

cnf(c_42,plain,
    ( r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2020,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,X1_50))
    | ~ r1_lattice3(sK3,X1_50,k2_yellow_0(sK3,X0_50))
    | ~ r2_yellow_0(sK3,X1_50)
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_4981,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r1_lattice3(sK3,k2_xboole_0(sK4,sK5),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_4982,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r1_lattice3(sK3,k2_xboole_0(sK4,sK5),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) != iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4981])).

cnf(c_5999,plain,
    ( r1_lattice3(sK3,k2_xboole_0(sK4,sK5),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_6004,plain,
    ( r1_lattice3(sK3,k2_xboole_0(sK4,sK5),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5999])).

cnf(c_9147,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9059,c_42,c_2301,c_4982,c_6004])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK1(X0,X1,X2,X3),X1)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1012,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X2,X3,X0,X1),X3)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_710])).

cnf(c_1013,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK1(X1,X2,sK3,X0),X2)
    | r2_yellow_0(sK3,k2_tarski(X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1333,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X2_49)
    | r2_yellow_0(sK3,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1013])).

cnf(c_1906,plain,
    ( r1_orders_2(sK3,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X2_49) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK1(X0,X1,X2,X3),X3)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1064,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X2,X3,X0,X1),X1)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_710])).

cnf(c_1065,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ r1_orders_2(sK3,sK1(X1,X2,sK3,X0),X0)
    | r2_yellow_0(sK3,k2_tarski(X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1064])).

cnf(c_1331,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | ~ r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X0_49)
    | r2_yellow_0(sK3,k2_tarski(X2_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1065])).

cnf(c_1908,plain,
    ( r1_orders_2(sK3,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK3,sK1(X1_49,X2_49,sK3,X0_49),X0_49) != iProver_top
    | r2_yellow_0(sK3,k2_tarski(X2_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_3830,plain,
    ( r1_orders_2(sK3,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK3,X0_49,X0_49) != iProver_top
    | r2_yellow_0(sK3,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1908])).

cnf(c_9154,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49) != iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9147,c_3830])).

cnf(c_9388,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)) = iProver_top
    | r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9154,c_2301])).

cnf(c_9389,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49) != iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9388])).

cnf(c_16,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_645,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_646,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X1)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_34])).

cnf(c_649,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X1)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k11_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_868,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0,X1),X1)
    | ~ r2_yellow_0(sK3,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_836,c_649])).

cnf(c_1341,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0_49,X1_49),X1_49)
    | ~ r2_yellow_0(sK3,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_868])).

cnf(c_1898,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,X0_49,X1_49),X1_49) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1341])).

cnf(c_7853,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7194,c_1898])).

cnf(c_8665,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = iProver_top
    | r2_yellow_0(sK3,k2_tarski(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7853,c_1412,c_2301])).

cnf(c_9397,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = iProver_top
    | r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9389,c_8665])).

cnf(c_1984,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_1985,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) = iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) != iProver_top
    | r2_yellow_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_9819,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)),k2_yellow_0(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9397,c_40,c_42,c_1412,c_1985])).

cnf(c_9823,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_9819])).

cnf(c_9838,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))
    | r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9823,c_3214])).

cnf(c_10040,plain,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9838,c_42,c_1412,c_2301,c_4982,c_6004])).

cnf(c_10047,plain,
    ( k2_yellow_0(sK3,k2_xboole_0(sK5,sK4)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_10040,c_7194])).

cnf(c_10228,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5)) = iProver_top
    | r2_yellow_0(sK3,k2_xboole_0(sK5,sK4)) != iProver_top
    | r2_yellow_0(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10047,c_1893])).

cnf(c_10254,plain,
    ( r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5))
    | ~ r2_yellow_0(sK3,k2_xboole_0(sK5,sK4))
    | ~ r2_yellow_0(sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10228])).

cnf(c_1371,plain,
    ( ~ r2_yellow_0(X0_48,X0_50)
    | r2_yellow_0(X0_48,X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_4979,plain,
    ( ~ r2_yellow_0(X0_48,k2_xboole_0(X0_50,X1_50))
    | r2_yellow_0(X0_48,k2_xboole_0(X1_50,X0_50)) ),
    inference(resolution,[status(thm)],[c_1359,c_1371])).

cnf(c_10074,plain,
    ( r2_yellow_0(sK3,k2_xboole_0(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_4979,c_1357])).

cnf(c_5763,plain,
    ( r1_lattice3(sK3,sK5,k2_yellow_0(sK3,sK5))
    | ~ r2_yellow_0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_4498,plain,
    ( m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X2))
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_879,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X5,u1_struct_0(sK3))
    | ~ m1_subset_1(X6,u1_struct_0(sK3))
    | m1_subset_1(sK1(X2,X3,X0,X1),u1_struct_0(X0))
    | X5 != X1
    | X4 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_710])).

cnf(c_880,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK1(X1,X2,sK3,X0),u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_1338,plain,
    ( ~ r1_orders_2(sK3,X0_49,X1_49)
    | ~ r1_orders_2(sK3,X0_49,X2_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK3))
    | m1_subset_1(sK1(X1_49,X2_49,sK3,X0_49),u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_49,X1_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_880])).

cnf(c_2146,plain,
    ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),X0_49)
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0_49,k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),X0_49) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_2355,plain,
    ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,X0_50))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | m1_subset_1(sK1(k2_yellow_0(sK3,X0_50),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,X0_50),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,X0_50)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_3080,plain,
    ( ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK5))
    | ~ r1_orders_2(sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),k2_yellow_0(sK3,sK4))
    | m1_subset_1(sK1(k2_yellow_0(sK3,sK5),k2_yellow_0(sK3,sK4),sK3,k2_yellow_0(sK3,k2_xboole_0(sK4,sK5))),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3))
    | k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) = k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_1411,plain,
    ( m1_subset_1(k2_yellow_0(sK3,sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_1390,plain,
    ( r1_lattice3(sK3,sK4,k2_yellow_0(sK3,sK4))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_30,negated_conjecture,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) != k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1358,negated_conjecture,
    ( k11_lattice3(sK3,k2_yellow_0(sK3,sK4),k2_yellow_0(sK3,sK5)) != k2_yellow_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_32,negated_conjecture,
    ( r2_yellow_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39355,c_19745,c_17882,c_17832,c_17564,c_12799,c_12809,c_10254,c_10074,c_5763,c_4498,c_3080,c_2300,c_1984,c_1411,c_1390,c_1358,c_31,c_32,c_33])).


%------------------------------------------------------------------------------
