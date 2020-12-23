%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1563+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:53 EST 2020

% Result     : Theorem 51.68s
% Output     : CNFRefutation 51.68s
% Verified   : 
% Statistics : Number of formulae       :  231 (1197 expanded)
%              Number of clauses        :  154 ( 286 expanded)
%              Number of leaves         :   17 ( 308 expanded)
%              Depth                    :   19
%              Number of atoms          : 1278 (7653 expanded)
%              Number of equality atoms :  100 (1025 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,sK6)) != k13_lattice3(X0,X1,sK6)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK5,X2)) != k13_lattice3(X0,sK5,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X2)) != k13_lattice3(sK4,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK5,sK6)) != k13_lattice3(sK4,sK5,sK6)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f50,f49,f48])).

fof(f83,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK2(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK2(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK2(X0,X1))
              & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK5,sK6)) != k13_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_914,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_915,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0,X1),X2)
    | r1_orders_2(sK4,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_2618,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | r1_orders_2(sK4,X0_53,X2_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_915])).

cnf(c_95860,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK0(sK4,k2_tarski(X2_53,X3_53),k13_lattice3(sK4,X4_53,sK6)))
    | r1_orders_2(sK4,X0_53,sK0(sK4,k2_tarski(X2_53,X3_53),k13_lattice3(sK4,X4_53,sK6)))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X2_53,X3_53),k13_lattice3(sK4,X4_53,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_127516,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK0(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | r1_orders_2(sK4,X0_53,sK0(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_95860])).

cnf(c_178808,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | r1_orders_2(sK4,X0_53,sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_127516])).

cnf(c_178810,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | r1_orders_2(sK4,sK5,sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_178808])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_34,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_34,c_32])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X1,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_20,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_492,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_493,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | r1_orders_2(sK4,k13_lattice3(sK4,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X2),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | r1_orders_2(sK4,k13_lattice3(sK4,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X2),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_34,c_32])).

cnf(c_498,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | r1_orders_2(sK4,k13_lattice3(sK4,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X2),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_675,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | r1_orders_2(sK4,k13_lattice3(sK4,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_659,c_498])).

cnf(c_2626,plain,
    ( ~ r1_orders_2(sK4,X0_53,X1_53)
    | ~ r1_orders_2(sK4,X2_53,X1_53)
    | r1_orders_2(sK4,k13_lattice3(sK4,X0_53,X2_53),X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_675])).

cnf(c_88946,plain,
    ( r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK6,sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK5,sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_122390,plain,
    ( r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK6,sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK5,sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_88946])).

cnf(c_122392,plain,
    ( r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK6,sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ r1_orders_2(sK4,sK5,sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_122390])).

cnf(c_92029,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK1(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | r1_orders_2(sK4,X0_53,sK1(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(X2_53,sK6),k13_lattice3(sK4,sK6,X0_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_95430,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | r1_orders_2(sK4,X0_53,sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X0_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_92029])).

cnf(c_95432,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | r1_orders_2(sK4,sK5,sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_95430])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1014,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_1015,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0)
    | k1_yellow_0(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_2613,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_52,X0_53),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0_52)
    | k1_yellow_0(sK4,X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_1015])).

cnf(c_86930,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k2_tarski(X0_53,X1_53),X2_53),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = X2_53 ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_87168,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_86930])).

cnf(c_91491,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,sK6))
    | k1_yellow_0(sK4,k2_tarski(X0_53,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_87168])).

cnf(c_91493,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(sK5,sK6))
    | k1_yellow_0(sK4,k2_tarski(sK5,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_91491])).

cnf(c_90033,plain,
    ( ~ r1_orders_2(sK4,X0_53,sK1(sK4,k2_tarski(X1_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | r1_orders_2(sK4,k13_lattice3(sK4,sK6,X0_53),sK1(sK4,k2_tarski(X1_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | ~ r1_orders_2(sK4,sK6,sK1(sK4,k2_tarski(X1_53,sK6),k13_lattice3(sK4,sK6,X0_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(X1_53,sK6),k13_lattice3(sK4,sK6,X0_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_90035,plain,
    ( r1_orders_2(sK4,k13_lattice3(sK4,sK6,sK5),sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ r1_orders_2(sK4,sK6,sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ r1_orders_2(sK4,sK5,sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_90033])).

cnf(c_24,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_935,plain,
    ( ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_936,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0,X1),X2)
    | r1_orders_2(sK4,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_2617,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | r1_orders_2(sK4,X1_53,X2_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_936])).

cnf(c_87041,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),X1_53)
    | r1_orders_2(sK4,sK6,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_89920,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)))
    | r1_orders_2(sK4,sK6,sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_87041])).

cnf(c_89922,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | r1_orders_2(sK4,sK6,sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ m1_subset_1(sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_89920])).

cnf(c_89174,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | r1_orders_2(sK4,sK6,sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_87041])).

cnf(c_89180,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | r1_orders_2(sK4,sK6,sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_89174])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1035,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_32])).

cnf(c_1036,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r2_lattice3(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0)
    | k1_yellow_0(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1035])).

cnf(c_2612,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | r2_lattice3(sK4,X0_52,sK0(sK4,X0_52,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0_52)
    | k1_yellow_0(sK4,X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_1036])).

cnf(c_86928,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK0(sK4,k2_tarski(X0_53,X1_53),X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = X2_53 ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_87166,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6))
    | r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_86928])).

cnf(c_89169,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6))
    | r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,sK6))
    | k1_yellow_0(sK4,k2_tarski(X0_53,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_87166])).

cnf(c_89176,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6))
    | r2_lattice3(sK4,k2_tarski(sK5,sK6),sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(sK5,sK6))
    | k1_yellow_0(sK4,k2_tarski(sK5,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_89169])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1056,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_32])).

cnf(c_1057,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X1,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0)
    | k1_yellow_0(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1056])).

cnf(c_2611,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | ~ r1_orders_2(sK4,X0_53,sK0(sK4,X0_52,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,X0_52)
    | k1_yellow_0(sK4,X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_1057])).

cnf(c_86929,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | ~ r1_orders_2(sK4,X2_53,sK0(sK4,k2_tarski(X0_53,X1_53),X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = X2_53 ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_87167,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,X1_53))
    | k1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_86929])).

cnf(c_87851,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(X0_53,sK6))
    | k1_yellow_0(sK4,k2_tarski(X0_53,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_87167])).

cnf(c_87854,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,k13_lattice3(sK4,sK5,sK6),sK0(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k2_tarski(sK5,sK6))
    | k1_yellow_0(sK4,k2_tarski(sK5,sK6)) = k13_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_87851])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_864,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_865,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X1,sK1(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_869,plain,
    ( r1_yellow_0(sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,X1,sK1(sK4,X0,X1))
    | ~ r2_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_32])).

cnf(c_870,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X1,sK1(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_869])).

cnf(c_2619,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | ~ r1_orders_2(sK4,X0_53,sK1(sK4,X0_52,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_870])).

cnf(c_86889,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | ~ r1_orders_2(sK4,X2_53,sK1(sK4,k2_tarski(X0_53,X1_53),X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_87378,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),X1_53)
    | ~ r1_orders_2(sK4,X1_53,sK1(sK4,k2_tarski(X0_53,sK6),X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_86889])).

cnf(c_87825,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53))
    | ~ r1_orders_2(sK4,k13_lattice3(sK4,sK6,X1_53),sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,X1_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_87378])).

cnf(c_87827,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5))
    | ~ r1_orders_2(sK4,k13_lattice3(sK4,sK6,sK5),sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,sK5),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_87825])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_840,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_841,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r2_lattice3(sK4,X0,sK1(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_845,plain,
    ( r1_yellow_0(sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_lattice3(sK4,X0,sK1(sK4,X0,X1))
    | ~ r2_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_32])).

cnf(c_846,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r2_lattice3(sK4,X0,sK1(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_845])).

cnf(c_2620,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | r2_lattice3(sK4,X0_52,sK1(sK4,X0_52,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_846])).

cnf(c_86888,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | r2_lattice3(sK4,k2_tarski(X0_53,X1_53),sK1(sK4,k2_tarski(X0_53,X1_53),X2_53))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_87377,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),X1_53)
    | r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK1(sK4,k2_tarski(X0_53,sK6),X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_86888])).

cnf(c_87799,plain,
    ( r2_lattice3(sK4,k2_tarski(X0_53,sK6),sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)))
    | ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,X1_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_87377])).

cnf(c_87801,plain,
    ( r2_lattice3(sK4,k2_tarski(sK5,sK6),sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)))
    | ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,sK5),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_87799])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_816,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_817,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_821,plain,
    ( r1_yellow_0(sK4,X0)
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_32])).

cnf(c_822,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_821])).

cnf(c_2621,plain,
    ( ~ r2_lattice3(sK4,X0_52,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_52,X0_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_86890,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,k2_tarski(X0_53,X1_53),X2_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_87379,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,k2_tarski(X0_53,sK6),X1_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_86890])).

cnf(c_87777,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53))
    | m1_subset_1(sK1(sK4,k2_tarski(X0_53,sK6),k13_lattice3(sK4,sK6,X1_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,X1_53),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_53,sK6)) ),
    inference(instantiation,[status(thm)],[c_87379])).

cnf(c_87782,plain,
    ( ~ r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5))
    | m1_subset_1(sK1(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,sK5),u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_87777])).

cnf(c_23,plain,
    ( r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_954,plain,
    ( r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_955,plain,
    ( r2_lattice3(sK4,k2_tarski(X0,X1),X2)
    | ~ r1_orders_2(sK4,X0,X2)
    | ~ r1_orders_2(sK4,X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_2616,plain,
    ( r2_lattice3(sK4,k2_tarski(X0_53,X1_53),X2_53)
    | ~ r1_orders_2(sK4,X0_53,X2_53)
    | ~ r1_orders_2(sK4,X1_53,X2_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_955])).

cnf(c_3204,plain,
    ( r2_lattice3(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,X2_53,X0_53))
    | ~ r1_orders_2(sK4,X0_53,k13_lattice3(sK4,X2_53,X0_53))
    | ~ r1_orders_2(sK4,X1_53,k13_lattice3(sK4,X2_53,X0_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X2_53,X0_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_5360,plain,
    ( r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,X0_53,sK5))
    | ~ r1_orders_2(sK4,sK6,k13_lattice3(sK4,X0_53,sK5))
    | ~ r1_orders_2(sK4,sK5,k13_lattice3(sK4,X0_53,sK5))
    | ~ m1_subset_1(k13_lattice3(sK4,X0_53,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3204])).

cnf(c_7492,plain,
    ( r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK6,sK5))
    | ~ r1_orders_2(sK4,sK6,k13_lattice3(sK4,sK6,sK5))
    | ~ r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK6,sK5))
    | ~ m1_subset_1(k13_lattice3(sK4,sK6,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_3181,plain,
    ( r2_lattice3(sK4,k2_tarski(X0_53,X1_53),k13_lattice3(sK4,X0_53,X2_53))
    | ~ r1_orders_2(sK4,X0_53,k13_lattice3(sK4,X0_53,X2_53))
    | ~ r1_orders_2(sK4,X1_53,k13_lattice3(sK4,X0_53,X2_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0_53,X2_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_5346,plain,
    ( r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,X0_53))
    | ~ r1_orders_2(sK4,sK6,k13_lattice3(sK4,sK5,X0_53))
    | ~ r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,X0_53))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,X0_53),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_7471,plain,
    ( r2_lattice3(sK4,k2_tarski(sK5,sK6),k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,sK6,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5346])).

cnf(c_2629,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X1_53,X0_53),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_7399,plain,
    ( m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2629])).

cnf(c_22,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_448,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_449,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_34,c_32])).

cnf(c_454,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_674,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_659,c_454])).

cnf(c_2627,plain,
    ( r1_orders_2(sK4,X0_53,k13_lattice3(sK4,X0_53,X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_674])).

cnf(c_7335,plain,
    ( r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2627])).

cnf(c_7098,plain,
    ( m1_subset_1(k13_lattice3(sK4,sK6,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2629])).

cnf(c_21,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_472,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_473,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X1,X0),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X1,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_34,c_32])).

cnf(c_476,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,X1,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_673,plain,
    ( r1_orders_2(sK4,X0,k13_lattice3(sK4,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_659,c_476])).

cnf(c_2628,plain,
    ( r1_orders_2(sK4,X0_53,k13_lattice3(sK4,X1_53,X0_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_673])).

cnf(c_5585,plain,
    ( r1_orders_2(sK4,sK6,k13_lattice3(sK4,X0_53,sK6))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_5589,plain,
    ( r1_orders_2(sK4,sK6,k13_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5585])).

cnf(c_5281,plain,
    ( r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK6,sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_4159,plain,
    ( r1_orders_2(sK4,sK6,k13_lattice3(sK4,sK6,sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2627])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2635,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3087,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2634,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_3088,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_373,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_8])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_391,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_373,c_0])).

cnf(c_437,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_391,c_33])).

cnf(c_438,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_93,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_96,plain,
    ( l1_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_117,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_440,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_33,c_32,c_93,c_96,c_117])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_440])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_2625,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),X0_53,X1_53) = k2_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_3097,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0_53,X1_53) = k2_tarski(X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_3482,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK5,X0_53) = k2_tarski(sK5,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_3097])).

cnf(c_3755,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK5,sK6) = k2_tarski(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_3087,c_3482])).

cnf(c_29,negated_conjecture,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK5,sK6)) != k13_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2636,negated_conjecture,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK5,sK6)) != k13_lattice3(sK4,sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3833,plain,
    ( k1_yellow_0(sK4,k2_tarski(sK5,sK6)) != k13_lattice3(sK4,sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_3755,c_2636])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_178810,c_122392,c_95432,c_91493,c_90035,c_89922,c_89180,c_89176,c_87854,c_87827,c_87801,c_87782,c_7492,c_7471,c_7399,c_7335,c_7098,c_5589,c_5281,c_4159,c_3833,c_30,c_31])).


%------------------------------------------------------------------------------
