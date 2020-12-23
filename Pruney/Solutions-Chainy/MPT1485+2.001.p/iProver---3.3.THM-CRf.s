%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:02 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 551 expanded)
%              Number of clauses        :  137 ( 172 expanded)
%              Number of leaves         :   27 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          : 1101 (3313 expanded)
%              Number of equality atoms :  165 ( 504 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK5)) != X1
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK4,k13_lattice3(X0,sK4,X2)) != sK4
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK3,X1,k13_lattice3(sK3,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v5_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f66,f65,f64])).

fof(f105,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
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
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
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
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
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
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK1(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3))
                        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0)
        & r2_hidden(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0)
              & r2_hidden(sK0(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,(
    k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_23,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_13,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_270,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_13])).

cnf(c_271,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_38,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_903,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_38])).

cnf(c_904,plain,
    ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_906,plain,
    ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_39,c_36])).

cnf(c_1428,plain,
    ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_906])).

cnf(c_1693,plain,
    ( r1_orders_2(sK3,X0_57,k10_lattice3(sK3,X0_57,X1_57))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1428])).

cnf(c_25749,plain,
    ( r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1733,plain,
    ( ~ r1_orders_2(X0_56,X0_57,X1_57)
    | r1_orders_2(X0_56,X2_57,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    theory(equality)).

cnf(c_2363,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | r1_orders_2(sK3,X2_57,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_2524,plain,
    ( r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X2_57,k10_lattice3(sK3,X2_57,X3_57))
    | X0_57 != X2_57
    | X1_57 != k10_lattice3(sK3,X2_57,X3_57) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_3180,plain,
    ( r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X1_57,X2_57))
    | ~ r1_orders_2(sK3,X1_57,k10_lattice3(sK3,X1_57,X2_57))
    | X0_57 != X1_57
    | k13_lattice3(sK3,X1_57,X2_57) != k10_lattice3(sK3,X1_57,X2_57) ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_25377,plain,
    ( r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
    | ~ r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
    | X0_57 != sK4
    | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3180])).

cnf(c_25384,plain,
    ( r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | ~ r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
    | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_25377])).

cnf(c_1725,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_23240,plain,
    ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X0_57
    | sK4 != X0_57
    | sK4 = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_23241,plain,
    ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4
    | sK4 = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_23240])).

cnf(c_2352,plain,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X0_57
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4
    | sK4 != X0_57 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_14389,plain,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4
    | sK4 != k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_26,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_14,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_251,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_14])).

cnf(c_252,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK2(X0,X2,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_1100,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_39])).

cnf(c_1101,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ l1_orders_2(sK3)
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1100])).

cnf(c_37,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1103,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1101,c_37,c_36])).

cnf(c_1104,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1103])).

cnf(c_1705,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,X2_57)
    | r1_orders_2(sK3,sK2(sK3,X2_57,X1_57,X0_57),X2_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_57,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1104])).

cnf(c_3727,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X2_57,X3_57))
    | r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57),X0_57),X1_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(k13_lattice3(sK3,X2_57,X3_57),u1_struct_0(sK3))
    | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_14315,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
    | r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,sK4,sK5),X0_57),X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_3727])).

cnf(c_14332,plain,
    ( r1_orders_2(sK3,sK2(sK3,sK4,k13_lattice3(sK3,sK4,sK5),sK4),sK4)
    | ~ r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | ~ r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_14315])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_263,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_14])).

cnf(c_264,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK2(X0,X2,X3,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_1034,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_264,c_39])).

cnf(c_1035,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ l1_orders_2(sK3)
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_1039,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1035,c_37,c_36])).

cnf(c_1040,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X0,X2)
    | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1039])).

cnf(c_1707,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,X2_57)
    | ~ r1_orders_2(sK3,sK2(sK3,X2_57,X1_57,X0_57),X0_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_57,u1_struct_0(sK3))
    | k11_lattice3(sK3,X2_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1040])).

cnf(c_3725,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X2_57,X3_57))
    | ~ r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57),X0_57),X0_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(k13_lattice3(sK3,X2_57,X3_57),u1_struct_0(sK3))
    | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_14316,plain,
    ( ~ r1_orders_2(sK3,X0_57,X1_57)
    | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
    | ~ r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,sK4,sK5),X0_57),X0_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_14328,plain,
    ( ~ r1_orders_2(sK3,sK2(sK3,sK4,k13_lattice3(sK3,sK4,sK5),sK4),sK4)
    | ~ r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | ~ r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_14316])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1239,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ l1_orders_2(sK3)
    | k11_lattice3(sK3,X0,X1) = k12_lattice3(sK3,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1239])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k11_lattice3(sK3,X0,X1) = k12_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1240,c_37,c_36])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k11_lattice3(sK3,X1,X0) = k12_lattice3(sK3,X1,X0) ),
    inference(renaming,[status(thm)],[c_1244])).

cnf(c_1700,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | k11_lattice3(sK3,X1_57,X0_57) = k12_lattice3(sK3,X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_1245])).

cnf(c_7098,plain,
    ( ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_2476,plain,
    ( X0_57 != X1_57
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X1_57
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2498,plain,
    ( X0_57 != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = X0_57
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_7097,plain,
    ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
    | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_1695,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | m1_subset_1(k10_lattice3(sK3,X0_57,X1_57),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1398])).

cnf(c_5941,plain,
    ( m1_subset_1(k10_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | m1_subset_1(X2_57,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    theory(equality)).

cnf(c_2482,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | k13_lattice3(sK3,sK4,sK5) != X0_57
    | u1_struct_0(sK3) != X1_57 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_3130,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | k13_lattice3(sK3,sK4,sK5) != X0_57
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_4825,plain,
    ( m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3130])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1721,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2268,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_12,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1354,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_1355,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_1354])).

cnf(c_1698,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_1355])).

cnf(c_2290,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1698])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1722,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2267,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_relat_1(X1_57) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

cnf(c_2610,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_2267])).

cnf(c_3966,plain,
    ( v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_2610])).

cnf(c_3967,plain,
    ( v1_relat_1(u1_orders_2(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3966])).

cnf(c_1724,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_3113,plain,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_3084,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1716,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2272,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1716])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1715,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_2273,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_924,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k13_lattice3(sK3,X0,X1) = k10_lattice3(sK3,X0,X1) ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k13_lattice3(sK3,X0,X1) = k10_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_39,c_36])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k13_lattice3(sK3,X1,X0) = k10_lattice3(sK3,X1,X0) ),
    inference(renaming,[status(thm)],[c_928])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | k13_lattice3(sK3,X1_57,X0_57) = k10_lattice3(sK3,X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_929])).

cnf(c_2279,plain,
    ( k13_lattice3(sK3,X0_57,X1_57) = k10_lattice3(sK3,X0_57,X1_57)
    | m1_subset_1(X1_57,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1709])).

cnf(c_2490,plain,
    ( k13_lattice3(sK3,sK4,X0_57) = k10_lattice3(sK3,sK4,X0_57)
    | m1_subset_1(X0_57,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2273,c_2279])).

cnf(c_3079,plain,
    ( k13_lattice3(sK3,sK4,sK5) = k10_lattice3(sK3,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2272,c_2490])).

cnf(c_8,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_554,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_40])).

cnf(c_555,plain,
    ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_113,plain,
    ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_557,plain,
    ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_40,c_36,c_113])).

cnf(c_1714,plain,
    ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_557])).

cnf(c_2274,plain,
    ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_5,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X2),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1718,plain,
    ( ~ r1_relat_2(X0_57,X1_57)
    | ~ r2_hidden(X2_57,X1_57)
    | r2_hidden(k4_tarski(X2_57,X2_57),X0_57)
    | ~ v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2271,plain,
    ( r1_relat_2(X0_57,X1_57) != iProver_top
    | r2_hidden(X2_57,X1_57) != iProver_top
    | r2_hidden(k4_tarski(X2_57,X2_57),X0_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1718])).

cnf(c_3005,plain,
    ( r2_hidden(X0_57,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0_57,X0_57),u1_orders_2(sK3)) = iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_2271])).

cnf(c_3006,plain,
    ( ~ r2_hidden(X0_57,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X0_57,X0_57),u1_orders_2(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3005])).

cnf(c_3008,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1379,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_36])).

cnf(c_1380,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_1379])).

cnf(c_1696,plain,
    ( r1_orders_2(sK3,X0_57,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0_57,X1_57),u1_orders_2(sK3)) ),
    inference(subtyping,[status(esa)],[c_1380])).

cnf(c_1808,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_513,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_581,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_513,c_13])).

cnf(c_707,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_581,c_38])).

cnf(c_708,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_95,plain,
    ( ~ v2_lattice3(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_104,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_117,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_710,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_37,c_36,c_95,c_104,c_117])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_710])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1341])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
    | r2_hidden(X0_57,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1342])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_33,negated_conjecture,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1717,negated_conjecture,
    ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1747,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25749,c_25384,c_23241,c_14389,c_14332,c_14328,c_7098,c_7097,c_5941,c_4825,c_3967,c_3113,c_3084,c_3079,c_3008,c_1808,c_1778,c_1717,c_1747,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 8.03/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.50  
% 8.03/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.50  
% 8.03/1.50  ------  iProver source info
% 8.03/1.50  
% 8.03/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.50  git: non_committed_changes: false
% 8.03/1.50  git: last_make_outside_of_git: false
% 8.03/1.50  
% 8.03/1.50  ------ 
% 8.03/1.50  
% 8.03/1.50  ------ Input Options
% 8.03/1.50  
% 8.03/1.50  --out_options                           all
% 8.03/1.50  --tptp_safe_out                         true
% 8.03/1.50  --problem_path                          ""
% 8.03/1.50  --include_path                          ""
% 8.03/1.50  --clausifier                            res/vclausify_rel
% 8.03/1.50  --clausifier_options                    ""
% 8.03/1.50  --stdin                                 false
% 8.03/1.50  --stats_out                             all
% 8.03/1.50  
% 8.03/1.50  ------ General Options
% 8.03/1.50  
% 8.03/1.50  --fof                                   false
% 8.03/1.50  --time_out_real                         305.
% 8.03/1.50  --time_out_virtual                      -1.
% 8.03/1.50  --symbol_type_check                     false
% 8.03/1.50  --clausify_out                          false
% 8.03/1.50  --sig_cnt_out                           false
% 8.03/1.50  --trig_cnt_out                          false
% 8.03/1.50  --trig_cnt_out_tolerance                1.
% 8.03/1.50  --trig_cnt_out_sk_spl                   false
% 8.03/1.50  --abstr_cl_out                          false
% 8.03/1.50  
% 8.03/1.50  ------ Global Options
% 8.03/1.50  
% 8.03/1.50  --schedule                              default
% 8.03/1.50  --add_important_lit                     false
% 8.03/1.50  --prop_solver_per_cl                    1000
% 8.03/1.50  --min_unsat_core                        false
% 8.03/1.50  --soft_assumptions                      false
% 8.03/1.50  --soft_lemma_size                       3
% 8.03/1.50  --prop_impl_unit_size                   0
% 8.03/1.50  --prop_impl_unit                        []
% 8.03/1.50  --share_sel_clauses                     true
% 8.03/1.50  --reset_solvers                         false
% 8.03/1.50  --bc_imp_inh                            [conj_cone]
% 8.03/1.50  --conj_cone_tolerance                   3.
% 8.03/1.50  --extra_neg_conj                        none
% 8.03/1.50  --large_theory_mode                     true
% 8.03/1.50  --prolific_symb_bound                   200
% 8.03/1.50  --lt_threshold                          2000
% 8.03/1.50  --clause_weak_htbl                      true
% 8.03/1.50  --gc_record_bc_elim                     false
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing Options
% 8.03/1.50  
% 8.03/1.50  --preprocessing_flag                    true
% 8.03/1.50  --time_out_prep_mult                    0.1
% 8.03/1.50  --splitting_mode                        input
% 8.03/1.50  --splitting_grd                         true
% 8.03/1.50  --splitting_cvd                         false
% 8.03/1.50  --splitting_cvd_svl                     false
% 8.03/1.50  --splitting_nvd                         32
% 8.03/1.50  --sub_typing                            true
% 8.03/1.50  --prep_gs_sim                           true
% 8.03/1.50  --prep_unflatten                        true
% 8.03/1.50  --prep_res_sim                          true
% 8.03/1.50  --prep_upred                            true
% 8.03/1.50  --prep_sem_filter                       exhaustive
% 8.03/1.50  --prep_sem_filter_out                   false
% 8.03/1.50  --pred_elim                             true
% 8.03/1.50  --res_sim_input                         true
% 8.03/1.50  --eq_ax_congr_red                       true
% 8.03/1.50  --pure_diseq_elim                       true
% 8.03/1.50  --brand_transform                       false
% 8.03/1.50  --non_eq_to_eq                          false
% 8.03/1.50  --prep_def_merge                        true
% 8.03/1.50  --prep_def_merge_prop_impl              false
% 8.03/1.50  --prep_def_merge_mbd                    true
% 8.03/1.50  --prep_def_merge_tr_red                 false
% 8.03/1.50  --prep_def_merge_tr_cl                  false
% 8.03/1.50  --smt_preprocessing                     true
% 8.03/1.50  --smt_ac_axioms                         fast
% 8.03/1.50  --preprocessed_out                      false
% 8.03/1.50  --preprocessed_stats                    false
% 8.03/1.50  
% 8.03/1.50  ------ Abstraction refinement Options
% 8.03/1.50  
% 8.03/1.50  --abstr_ref                             []
% 8.03/1.50  --abstr_ref_prep                        false
% 8.03/1.50  --abstr_ref_until_sat                   false
% 8.03/1.50  --abstr_ref_sig_restrict                funpre
% 8.03/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.50  --abstr_ref_under                       []
% 8.03/1.50  
% 8.03/1.50  ------ SAT Options
% 8.03/1.50  
% 8.03/1.50  --sat_mode                              false
% 8.03/1.50  --sat_fm_restart_options                ""
% 8.03/1.50  --sat_gr_def                            false
% 8.03/1.50  --sat_epr_types                         true
% 8.03/1.50  --sat_non_cyclic_types                  false
% 8.03/1.50  --sat_finite_models                     false
% 8.03/1.50  --sat_fm_lemmas                         false
% 8.03/1.50  --sat_fm_prep                           false
% 8.03/1.50  --sat_fm_uc_incr                        true
% 8.03/1.50  --sat_out_model                         small
% 8.03/1.50  --sat_out_clauses                       false
% 8.03/1.50  
% 8.03/1.50  ------ QBF Options
% 8.03/1.50  
% 8.03/1.50  --qbf_mode                              false
% 8.03/1.50  --qbf_elim_univ                         false
% 8.03/1.50  --qbf_dom_inst                          none
% 8.03/1.50  --qbf_dom_pre_inst                      false
% 8.03/1.50  --qbf_sk_in                             false
% 8.03/1.50  --qbf_pred_elim                         true
% 8.03/1.50  --qbf_split                             512
% 8.03/1.50  
% 8.03/1.50  ------ BMC1 Options
% 8.03/1.50  
% 8.03/1.50  --bmc1_incremental                      false
% 8.03/1.50  --bmc1_axioms                           reachable_all
% 8.03/1.50  --bmc1_min_bound                        0
% 8.03/1.50  --bmc1_max_bound                        -1
% 8.03/1.50  --bmc1_max_bound_default                -1
% 8.03/1.50  --bmc1_symbol_reachability              true
% 8.03/1.50  --bmc1_property_lemmas                  false
% 8.03/1.50  --bmc1_k_induction                      false
% 8.03/1.50  --bmc1_non_equiv_states                 false
% 8.03/1.50  --bmc1_deadlock                         false
% 8.03/1.50  --bmc1_ucm                              false
% 8.03/1.50  --bmc1_add_unsat_core                   none
% 8.03/1.50  --bmc1_unsat_core_children              false
% 8.03/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.50  --bmc1_out_stat                         full
% 8.03/1.50  --bmc1_ground_init                      false
% 8.03/1.50  --bmc1_pre_inst_next_state              false
% 8.03/1.50  --bmc1_pre_inst_state                   false
% 8.03/1.50  --bmc1_pre_inst_reach_state             false
% 8.03/1.50  --bmc1_out_unsat_core                   false
% 8.03/1.50  --bmc1_aig_witness_out                  false
% 8.03/1.50  --bmc1_verbose                          false
% 8.03/1.50  --bmc1_dump_clauses_tptp                false
% 8.03/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.50  --bmc1_dump_file                        -
% 8.03/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.50  --bmc1_ucm_extend_mode                  1
% 8.03/1.50  --bmc1_ucm_init_mode                    2
% 8.03/1.50  --bmc1_ucm_cone_mode                    none
% 8.03/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.50  --bmc1_ucm_relax_model                  4
% 8.03/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.50  --bmc1_ucm_layered_model                none
% 8.03/1.50  --bmc1_ucm_max_lemma_size               10
% 8.03/1.50  
% 8.03/1.50  ------ AIG Options
% 8.03/1.50  
% 8.03/1.50  --aig_mode                              false
% 8.03/1.50  
% 8.03/1.50  ------ Instantiation Options
% 8.03/1.50  
% 8.03/1.50  --instantiation_flag                    true
% 8.03/1.50  --inst_sos_flag                         true
% 8.03/1.50  --inst_sos_phase                        true
% 8.03/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.50  --inst_lit_sel_side                     num_symb
% 8.03/1.50  --inst_solver_per_active                1400
% 8.03/1.50  --inst_solver_calls_frac                1.
% 8.03/1.50  --inst_passive_queue_type               priority_queues
% 8.03/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.50  --inst_passive_queues_freq              [25;2]
% 8.03/1.50  --inst_dismatching                      true
% 8.03/1.50  --inst_eager_unprocessed_to_passive     true
% 8.03/1.50  --inst_prop_sim_given                   true
% 8.03/1.50  --inst_prop_sim_new                     false
% 8.03/1.50  --inst_subs_new                         false
% 8.03/1.50  --inst_eq_res_simp                      false
% 8.03/1.50  --inst_subs_given                       false
% 8.03/1.50  --inst_orphan_elimination               true
% 8.03/1.50  --inst_learning_loop_flag               true
% 8.03/1.50  --inst_learning_start                   3000
% 8.03/1.50  --inst_learning_factor                  2
% 8.03/1.50  --inst_start_prop_sim_after_learn       3
% 8.03/1.50  --inst_sel_renew                        solver
% 8.03/1.50  --inst_lit_activity_flag                true
% 8.03/1.50  --inst_restr_to_given                   false
% 8.03/1.50  --inst_activity_threshold               500
% 8.03/1.50  --inst_out_proof                        true
% 8.03/1.50  
% 8.03/1.50  ------ Resolution Options
% 8.03/1.50  
% 8.03/1.50  --resolution_flag                       true
% 8.03/1.50  --res_lit_sel                           adaptive
% 8.03/1.50  --res_lit_sel_side                      none
% 8.03/1.50  --res_ordering                          kbo
% 8.03/1.50  --res_to_prop_solver                    active
% 8.03/1.50  --res_prop_simpl_new                    false
% 8.03/1.50  --res_prop_simpl_given                  true
% 8.03/1.50  --res_passive_queue_type                priority_queues
% 8.03/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.50  --res_passive_queues_freq               [15;5]
% 8.03/1.50  --res_forward_subs                      full
% 8.03/1.50  --res_backward_subs                     full
% 8.03/1.50  --res_forward_subs_resolution           true
% 8.03/1.50  --res_backward_subs_resolution          true
% 8.03/1.50  --res_orphan_elimination                true
% 8.03/1.50  --res_time_limit                        2.
% 8.03/1.50  --res_out_proof                         true
% 8.03/1.50  
% 8.03/1.50  ------ Superposition Options
% 8.03/1.50  
% 8.03/1.50  --superposition_flag                    true
% 8.03/1.50  --sup_passive_queue_type                priority_queues
% 8.03/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.50  --demod_completeness_check              fast
% 8.03/1.50  --demod_use_ground                      true
% 8.03/1.50  --sup_to_prop_solver                    passive
% 8.03/1.50  --sup_prop_simpl_new                    true
% 8.03/1.50  --sup_prop_simpl_given                  true
% 8.03/1.50  --sup_fun_splitting                     true
% 8.03/1.50  --sup_smt_interval                      50000
% 8.03/1.50  
% 8.03/1.50  ------ Superposition Simplification Setup
% 8.03/1.50  
% 8.03/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.50  --sup_immed_triv                        [TrivRules]
% 8.03/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_immed_bw_main                     []
% 8.03/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_input_bw                          []
% 8.03/1.50  
% 8.03/1.50  ------ Combination Options
% 8.03/1.50  
% 8.03/1.50  --comb_res_mult                         3
% 8.03/1.50  --comb_sup_mult                         2
% 8.03/1.50  --comb_inst_mult                        10
% 8.03/1.50  
% 8.03/1.50  ------ Debug Options
% 8.03/1.50  
% 8.03/1.50  --dbg_backtrace                         false
% 8.03/1.50  --dbg_dump_prop_clauses                 false
% 8.03/1.50  --dbg_dump_prop_clauses_file            -
% 8.03/1.50  --dbg_out_stat                          false
% 8.03/1.50  ------ Parsing...
% 8.03/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.50  ------ Proving...
% 8.03/1.50  ------ Problem Properties 
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  clauses                                 31
% 8.03/1.50  conjectures                             3
% 8.03/1.50  EPR                                     0
% 8.03/1.50  Horn                                    24
% 8.03/1.50  unary                                   6
% 8.03/1.50  binary                                  1
% 8.03/1.50  lits                                    124
% 8.03/1.50  lits eq                                 12
% 8.03/1.50  fd_pure                                 0
% 8.03/1.50  fd_pseudo                               0
% 8.03/1.50  fd_cond                                 0
% 8.03/1.50  fd_pseudo_cond                          8
% 8.03/1.50  AC symbols                              0
% 8.03/1.50  
% 8.03/1.50  ------ Schedule dynamic 5 is on 
% 8.03/1.50  
% 8.03/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  ------ 
% 8.03/1.50  Current options:
% 8.03/1.50  ------ 
% 8.03/1.50  
% 8.03/1.50  ------ Input Options
% 8.03/1.50  
% 8.03/1.50  --out_options                           all
% 8.03/1.50  --tptp_safe_out                         true
% 8.03/1.50  --problem_path                          ""
% 8.03/1.50  --include_path                          ""
% 8.03/1.50  --clausifier                            res/vclausify_rel
% 8.03/1.50  --clausifier_options                    ""
% 8.03/1.50  --stdin                                 false
% 8.03/1.50  --stats_out                             all
% 8.03/1.50  
% 8.03/1.50  ------ General Options
% 8.03/1.50  
% 8.03/1.50  --fof                                   false
% 8.03/1.50  --time_out_real                         305.
% 8.03/1.50  --time_out_virtual                      -1.
% 8.03/1.50  --symbol_type_check                     false
% 8.03/1.50  --clausify_out                          false
% 8.03/1.50  --sig_cnt_out                           false
% 8.03/1.50  --trig_cnt_out                          false
% 8.03/1.50  --trig_cnt_out_tolerance                1.
% 8.03/1.50  --trig_cnt_out_sk_spl                   false
% 8.03/1.50  --abstr_cl_out                          false
% 8.03/1.50  
% 8.03/1.50  ------ Global Options
% 8.03/1.50  
% 8.03/1.50  --schedule                              default
% 8.03/1.50  --add_important_lit                     false
% 8.03/1.50  --prop_solver_per_cl                    1000
% 8.03/1.50  --min_unsat_core                        false
% 8.03/1.50  --soft_assumptions                      false
% 8.03/1.50  --soft_lemma_size                       3
% 8.03/1.50  --prop_impl_unit_size                   0
% 8.03/1.50  --prop_impl_unit                        []
% 8.03/1.50  --share_sel_clauses                     true
% 8.03/1.50  --reset_solvers                         false
% 8.03/1.50  --bc_imp_inh                            [conj_cone]
% 8.03/1.50  --conj_cone_tolerance                   3.
% 8.03/1.50  --extra_neg_conj                        none
% 8.03/1.50  --large_theory_mode                     true
% 8.03/1.50  --prolific_symb_bound                   200
% 8.03/1.50  --lt_threshold                          2000
% 8.03/1.50  --clause_weak_htbl                      true
% 8.03/1.50  --gc_record_bc_elim                     false
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing Options
% 8.03/1.50  
% 8.03/1.50  --preprocessing_flag                    true
% 8.03/1.50  --time_out_prep_mult                    0.1
% 8.03/1.50  --splitting_mode                        input
% 8.03/1.50  --splitting_grd                         true
% 8.03/1.50  --splitting_cvd                         false
% 8.03/1.50  --splitting_cvd_svl                     false
% 8.03/1.50  --splitting_nvd                         32
% 8.03/1.50  --sub_typing                            true
% 8.03/1.50  --prep_gs_sim                           true
% 8.03/1.50  --prep_unflatten                        true
% 8.03/1.50  --prep_res_sim                          true
% 8.03/1.50  --prep_upred                            true
% 8.03/1.50  --prep_sem_filter                       exhaustive
% 8.03/1.50  --prep_sem_filter_out                   false
% 8.03/1.50  --pred_elim                             true
% 8.03/1.50  --res_sim_input                         true
% 8.03/1.50  --eq_ax_congr_red                       true
% 8.03/1.50  --pure_diseq_elim                       true
% 8.03/1.50  --brand_transform                       false
% 8.03/1.50  --non_eq_to_eq                          false
% 8.03/1.50  --prep_def_merge                        true
% 8.03/1.50  --prep_def_merge_prop_impl              false
% 8.03/1.50  --prep_def_merge_mbd                    true
% 8.03/1.50  --prep_def_merge_tr_red                 false
% 8.03/1.50  --prep_def_merge_tr_cl                  false
% 8.03/1.50  --smt_preprocessing                     true
% 8.03/1.50  --smt_ac_axioms                         fast
% 8.03/1.50  --preprocessed_out                      false
% 8.03/1.50  --preprocessed_stats                    false
% 8.03/1.50  
% 8.03/1.50  ------ Abstraction refinement Options
% 8.03/1.50  
% 8.03/1.50  --abstr_ref                             []
% 8.03/1.50  --abstr_ref_prep                        false
% 8.03/1.50  --abstr_ref_until_sat                   false
% 8.03/1.50  --abstr_ref_sig_restrict                funpre
% 8.03/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.50  --abstr_ref_under                       []
% 8.03/1.50  
% 8.03/1.50  ------ SAT Options
% 8.03/1.50  
% 8.03/1.50  --sat_mode                              false
% 8.03/1.50  --sat_fm_restart_options                ""
% 8.03/1.50  --sat_gr_def                            false
% 8.03/1.50  --sat_epr_types                         true
% 8.03/1.50  --sat_non_cyclic_types                  false
% 8.03/1.50  --sat_finite_models                     false
% 8.03/1.50  --sat_fm_lemmas                         false
% 8.03/1.50  --sat_fm_prep                           false
% 8.03/1.50  --sat_fm_uc_incr                        true
% 8.03/1.50  --sat_out_model                         small
% 8.03/1.50  --sat_out_clauses                       false
% 8.03/1.50  
% 8.03/1.50  ------ QBF Options
% 8.03/1.50  
% 8.03/1.50  --qbf_mode                              false
% 8.03/1.50  --qbf_elim_univ                         false
% 8.03/1.50  --qbf_dom_inst                          none
% 8.03/1.50  --qbf_dom_pre_inst                      false
% 8.03/1.50  --qbf_sk_in                             false
% 8.03/1.50  --qbf_pred_elim                         true
% 8.03/1.50  --qbf_split                             512
% 8.03/1.50  
% 8.03/1.50  ------ BMC1 Options
% 8.03/1.50  
% 8.03/1.50  --bmc1_incremental                      false
% 8.03/1.50  --bmc1_axioms                           reachable_all
% 8.03/1.50  --bmc1_min_bound                        0
% 8.03/1.50  --bmc1_max_bound                        -1
% 8.03/1.50  --bmc1_max_bound_default                -1
% 8.03/1.50  --bmc1_symbol_reachability              true
% 8.03/1.50  --bmc1_property_lemmas                  false
% 8.03/1.50  --bmc1_k_induction                      false
% 8.03/1.50  --bmc1_non_equiv_states                 false
% 8.03/1.50  --bmc1_deadlock                         false
% 8.03/1.50  --bmc1_ucm                              false
% 8.03/1.50  --bmc1_add_unsat_core                   none
% 8.03/1.50  --bmc1_unsat_core_children              false
% 8.03/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.50  --bmc1_out_stat                         full
% 8.03/1.50  --bmc1_ground_init                      false
% 8.03/1.50  --bmc1_pre_inst_next_state              false
% 8.03/1.50  --bmc1_pre_inst_state                   false
% 8.03/1.50  --bmc1_pre_inst_reach_state             false
% 8.03/1.50  --bmc1_out_unsat_core                   false
% 8.03/1.50  --bmc1_aig_witness_out                  false
% 8.03/1.50  --bmc1_verbose                          false
% 8.03/1.50  --bmc1_dump_clauses_tptp                false
% 8.03/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.50  --bmc1_dump_file                        -
% 8.03/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.50  --bmc1_ucm_extend_mode                  1
% 8.03/1.50  --bmc1_ucm_init_mode                    2
% 8.03/1.50  --bmc1_ucm_cone_mode                    none
% 8.03/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.50  --bmc1_ucm_relax_model                  4
% 8.03/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.50  --bmc1_ucm_layered_model                none
% 8.03/1.50  --bmc1_ucm_max_lemma_size               10
% 8.03/1.50  
% 8.03/1.50  ------ AIG Options
% 8.03/1.50  
% 8.03/1.50  --aig_mode                              false
% 8.03/1.50  
% 8.03/1.50  ------ Instantiation Options
% 8.03/1.50  
% 8.03/1.50  --instantiation_flag                    true
% 8.03/1.50  --inst_sos_flag                         true
% 8.03/1.50  --inst_sos_phase                        true
% 8.03/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.50  --inst_lit_sel_side                     none
% 8.03/1.50  --inst_solver_per_active                1400
% 8.03/1.50  --inst_solver_calls_frac                1.
% 8.03/1.50  --inst_passive_queue_type               priority_queues
% 8.03/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.50  --inst_passive_queues_freq              [25;2]
% 8.03/1.50  --inst_dismatching                      true
% 8.03/1.50  --inst_eager_unprocessed_to_passive     true
% 8.03/1.50  --inst_prop_sim_given                   true
% 8.03/1.50  --inst_prop_sim_new                     false
% 8.03/1.50  --inst_subs_new                         false
% 8.03/1.50  --inst_eq_res_simp                      false
% 8.03/1.50  --inst_subs_given                       false
% 8.03/1.50  --inst_orphan_elimination               true
% 8.03/1.50  --inst_learning_loop_flag               true
% 8.03/1.50  --inst_learning_start                   3000
% 8.03/1.50  --inst_learning_factor                  2
% 8.03/1.50  --inst_start_prop_sim_after_learn       3
% 8.03/1.50  --inst_sel_renew                        solver
% 8.03/1.50  --inst_lit_activity_flag                true
% 8.03/1.50  --inst_restr_to_given                   false
% 8.03/1.50  --inst_activity_threshold               500
% 8.03/1.50  --inst_out_proof                        true
% 8.03/1.50  
% 8.03/1.50  ------ Resolution Options
% 8.03/1.50  
% 8.03/1.50  --resolution_flag                       false
% 8.03/1.50  --res_lit_sel                           adaptive
% 8.03/1.50  --res_lit_sel_side                      none
% 8.03/1.50  --res_ordering                          kbo
% 8.03/1.50  --res_to_prop_solver                    active
% 8.03/1.50  --res_prop_simpl_new                    false
% 8.03/1.50  --res_prop_simpl_given                  true
% 8.03/1.50  --res_passive_queue_type                priority_queues
% 8.03/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.50  --res_passive_queues_freq               [15;5]
% 8.03/1.50  --res_forward_subs                      full
% 8.03/1.50  --res_backward_subs                     full
% 8.03/1.50  --res_forward_subs_resolution           true
% 8.03/1.50  --res_backward_subs_resolution          true
% 8.03/1.50  --res_orphan_elimination                true
% 8.03/1.50  --res_time_limit                        2.
% 8.03/1.50  --res_out_proof                         true
% 8.03/1.50  
% 8.03/1.50  ------ Superposition Options
% 8.03/1.50  
% 8.03/1.50  --superposition_flag                    true
% 8.03/1.50  --sup_passive_queue_type                priority_queues
% 8.03/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.50  --demod_completeness_check              fast
% 8.03/1.50  --demod_use_ground                      true
% 8.03/1.50  --sup_to_prop_solver                    passive
% 8.03/1.50  --sup_prop_simpl_new                    true
% 8.03/1.50  --sup_prop_simpl_given                  true
% 8.03/1.50  --sup_fun_splitting                     true
% 8.03/1.50  --sup_smt_interval                      50000
% 8.03/1.50  
% 8.03/1.50  ------ Superposition Simplification Setup
% 8.03/1.50  
% 8.03/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.50  --sup_immed_triv                        [TrivRules]
% 8.03/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_immed_bw_main                     []
% 8.03/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.50  --sup_input_bw                          []
% 8.03/1.50  
% 8.03/1.50  ------ Combination Options
% 8.03/1.50  
% 8.03/1.50  --comb_res_mult                         3
% 8.03/1.50  --comb_sup_mult                         2
% 8.03/1.50  --comb_inst_mult                        10
% 8.03/1.50  
% 8.03/1.50  ------ Debug Options
% 8.03/1.50  
% 8.03/1.50  --dbg_backtrace                         false
% 8.03/1.50  --dbg_dump_prop_clauses                 false
% 8.03/1.50  --dbg_dump_prop_clauses_file            -
% 8.03/1.50  --dbg_out_stat                          false
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  ------ Proving...
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  % SZS status Theorem for theBenchmark.p
% 8.03/1.50  
% 8.03/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.50  
% 8.03/1.50  fof(f13,axiom,(
% 8.03/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f36,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f13])).
% 8.03/1.50  
% 8.03/1.50  fof(f37,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f36])).
% 8.03/1.50  
% 8.03/1.50  fof(f84,plain,(
% 8.03/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f37])).
% 8.03/1.50  
% 8.03/1.50  fof(f18,conjecture,(
% 8.03/1.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f19,negated_conjecture,(
% 8.03/1.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 8.03/1.50    inference(negated_conjecture,[],[f18])).
% 8.03/1.50  
% 8.03/1.50  fof(f46,plain,(
% 8.03/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f19])).
% 8.03/1.50  
% 8.03/1.50  fof(f47,plain,(
% 8.03/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f46])).
% 8.03/1.50  
% 8.03/1.50  fof(f66,plain,(
% 8.03/1.50    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK5)) != X1 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f65,plain,(
% 8.03/1.50    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK4,k13_lattice3(X0,sK4,X2)) != sK4 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f64,plain,(
% 8.03/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK3,X1,k13_lattice3(sK3,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3))),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f67,plain,(
% 8.03/1.50    ((k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3)),
% 8.03/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f66,f65,f64])).
% 8.03/1.50  
% 8.03/1.50  fof(f105,plain,(
% 8.03/1.50    l1_orders_2(sK3)),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f14,axiom,(
% 8.03/1.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f38,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f14])).
% 8.03/1.50  
% 8.03/1.50  fof(f39,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(flattening,[],[f38])).
% 8.03/1.50  
% 8.03/1.50  fof(f54,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(nnf_transformation,[],[f39])).
% 8.03/1.50  
% 8.03/1.50  fof(f55,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(flattening,[],[f54])).
% 8.03/1.50  
% 8.03/1.50  fof(f56,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(rectify,[],[f55])).
% 8.03/1.50  
% 8.03/1.50  fof(f57,plain,(
% 8.03/1.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK1(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f58,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK1(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK1(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 8.03/1.50  
% 8.03/1.50  fof(f85,plain,(
% 8.03/1.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f58])).
% 8.03/1.50  
% 8.03/1.50  fof(f111,plain,(
% 8.03/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.03/1.50    inference(equality_resolution,[],[f85])).
% 8.03/1.50  
% 8.03/1.50  fof(f10,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f30,plain,(
% 8.03/1.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f10])).
% 8.03/1.50  
% 8.03/1.50  fof(f31,plain,(
% 8.03/1.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f30])).
% 8.03/1.50  
% 8.03/1.50  fof(f81,plain,(
% 8.03/1.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f31])).
% 8.03/1.50  
% 8.03/1.50  fof(f103,plain,(
% 8.03/1.50    v1_lattice3(sK3)),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f102,plain,(
% 8.03/1.50    v5_orders_2(sK3)),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f15,axiom,(
% 8.03/1.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f40,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f15])).
% 8.03/1.50  
% 8.03/1.50  fof(f41,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(flattening,[],[f40])).
% 8.03/1.50  
% 8.03/1.50  fof(f59,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(nnf_transformation,[],[f41])).
% 8.03/1.50  
% 8.03/1.50  fof(f60,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(flattening,[],[f59])).
% 8.03/1.50  
% 8.03/1.50  fof(f61,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(rectify,[],[f60])).
% 8.03/1.50  
% 8.03/1.50  fof(f62,plain,(
% 8.03/1.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))))),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f63,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK2(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).
% 8.03/1.50  
% 8.03/1.50  fof(f96,plain,(
% 8.03/1.50    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f63])).
% 8.03/1.50  
% 8.03/1.50  fof(f11,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f32,plain,(
% 8.03/1.50    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f11])).
% 8.03/1.50  
% 8.03/1.50  fof(f33,plain,(
% 8.03/1.50    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f32])).
% 8.03/1.50  
% 8.03/1.50  fof(f82,plain,(
% 8.03/1.50    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f33])).
% 8.03/1.50  
% 8.03/1.50  fof(f104,plain,(
% 8.03/1.50    v2_lattice3(sK3)),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f98,plain,(
% 8.03/1.50    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK2(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f63])).
% 8.03/1.50  
% 8.03/1.50  fof(f16,axiom,(
% 8.03/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f42,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f16])).
% 8.03/1.50  
% 8.03/1.50  fof(f43,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f42])).
% 8.03/1.50  
% 8.03/1.50  fof(f99,plain,(
% 8.03/1.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f43])).
% 8.03/1.50  
% 8.03/1.50  fof(f3,axiom,(
% 8.03/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f70,plain,(
% 8.03/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.03/1.50    inference(cnf_transformation,[],[f3])).
% 8.03/1.50  
% 8.03/1.50  fof(f9,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f29,plain,(
% 8.03/1.50    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f9])).
% 8.03/1.50  
% 8.03/1.50  fof(f80,plain,(
% 8.03/1.50    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f29])).
% 8.03/1.50  
% 8.03/1.50  fof(f2,axiom,(
% 8.03/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f22,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f2])).
% 8.03/1.50  
% 8.03/1.50  fof(f69,plain,(
% 8.03/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f22])).
% 8.03/1.50  
% 8.03/1.50  fof(f107,plain,(
% 8.03/1.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f106,plain,(
% 8.03/1.50    m1_subset_1(sK4,u1_struct_0(sK3))),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f17,axiom,(
% 8.03/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f44,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f17])).
% 8.03/1.50  
% 8.03/1.50  fof(f45,plain,(
% 8.03/1.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 8.03/1.50    inference(flattening,[],[f44])).
% 8.03/1.50  
% 8.03/1.50  fof(f100,plain,(
% 8.03/1.50    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f45])).
% 8.03/1.50  
% 8.03/1.50  fof(f6,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f26,plain,(
% 8.03/1.50    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f6])).
% 8.03/1.50  
% 8.03/1.50  fof(f52,plain,(
% 8.03/1.50    ! [X0] : (((v3_orders_2(X0) | ~r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0))) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(nnf_transformation,[],[f26])).
% 8.03/1.50  
% 8.03/1.50  fof(f75,plain,(
% 8.03/1.50    ( ! [X0] : (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f52])).
% 8.03/1.50  
% 8.03/1.50  fof(f101,plain,(
% 8.03/1.50    v3_orders_2(sK3)),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  fof(f4,axiom,(
% 8.03/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f23,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f4])).
% 8.03/1.50  
% 8.03/1.50  fof(f48,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 8.03/1.50    inference(nnf_transformation,[],[f23])).
% 8.03/1.50  
% 8.03/1.50  fof(f49,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 8.03/1.50    inference(rectify,[],[f48])).
% 8.03/1.50  
% 8.03/1.50  fof(f50,plain,(
% 8.03/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0) & r2_hidden(sK0(X0,X1),X1)))),
% 8.03/1.50    introduced(choice_axiom,[])).
% 8.03/1.50  
% 8.03/1.50  fof(f51,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0) & r2_hidden(sK0(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 8.03/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 8.03/1.50  
% 8.03/1.50  fof(f71,plain,(
% 8.03/1.50    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f51])).
% 8.03/1.50  
% 8.03/1.50  fof(f7,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f27,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f7])).
% 8.03/1.50  
% 8.03/1.50  fof(f53,plain,(
% 8.03/1.50    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(nnf_transformation,[],[f27])).
% 8.03/1.50  
% 8.03/1.50  fof(f78,plain,(
% 8.03/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f53])).
% 8.03/1.50  
% 8.03/1.50  fof(f1,axiom,(
% 8.03/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f20,plain,(
% 8.03/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 8.03/1.50    inference(ennf_transformation,[],[f1])).
% 8.03/1.50  
% 8.03/1.50  fof(f21,plain,(
% 8.03/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 8.03/1.50    inference(flattening,[],[f20])).
% 8.03/1.50  
% 8.03/1.50  fof(f68,plain,(
% 8.03/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f21])).
% 8.03/1.50  
% 8.03/1.50  fof(f8,axiom,(
% 8.03/1.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f28,plain,(
% 8.03/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 8.03/1.50    inference(ennf_transformation,[],[f8])).
% 8.03/1.50  
% 8.03/1.50  fof(f79,plain,(
% 8.03/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f28])).
% 8.03/1.50  
% 8.03/1.50  fof(f5,axiom,(
% 8.03/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 8.03/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.50  
% 8.03/1.50  fof(f24,plain,(
% 8.03/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 8.03/1.50    inference(ennf_transformation,[],[f5])).
% 8.03/1.50  
% 8.03/1.50  fof(f25,plain,(
% 8.03/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 8.03/1.50    inference(flattening,[],[f24])).
% 8.03/1.50  
% 8.03/1.50  fof(f74,plain,(
% 8.03/1.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 8.03/1.50    inference(cnf_transformation,[],[f25])).
% 8.03/1.50  
% 8.03/1.50  fof(f108,plain,(
% 8.03/1.50    k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4),
% 8.03/1.50    inference(cnf_transformation,[],[f67])).
% 8.03/1.50  
% 8.03/1.50  cnf(c_16,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.03/1.50      | ~ l1_orders_2(X1) ),
% 8.03/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_36,negated_conjecture,
% 8.03/1.50      ( l1_orders_2(sK3) ),
% 8.03/1.50      inference(cnf_transformation,[],[f105]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1397,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.03/1.50      | sK3 != X1 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1398,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1397]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_23,plain,
% 8.03/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v1_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | v2_struct_0(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f111]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_13,plain,
% 8.03/1.50      ( ~ v1_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f81]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_270,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0)
% 8.03/1.50      | ~ v1_lattice3(X0)
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_23,c_13]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_271,plain,
% 8.03/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v1_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0) ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_270]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_38,negated_conjecture,
% 8.03/1.50      ( v1_lattice3(sK3) ),
% 8.03/1.50      inference(cnf_transformation,[],[f103]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_903,plain,
% 8.03/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_271,c_38]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_904,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3))
% 8.03/1.50      | ~ v5_orders_2(sK3)
% 8.03/1.50      | ~ l1_orders_2(sK3) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_903]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_39,negated_conjecture,
% 8.03/1.50      ( v5_orders_2(sK3) ),
% 8.03/1.50      inference(cnf_transformation,[],[f102]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_906,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(sK3,X0,X1),u1_struct_0(sK3)) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_904,c_39,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1428,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0,k10_lattice3(sK3,X0,X1))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(backward_subsumption_resolution,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_1398,c_906]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1693,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0_57,k10_lattice3(sK3,X0_57,X1_57))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1428]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_25749,plain,
% 8.03/1.50      ( r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1693]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1733,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0_56,X0_57,X1_57)
% 8.03/1.50      | r1_orders_2(X0_56,X2_57,X3_57)
% 8.03/1.50      | X2_57 != X0_57
% 8.03/1.50      | X3_57 != X1_57 ),
% 8.03/1.50      theory(equality) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2363,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | r1_orders_2(sK3,X2_57,X3_57)
% 8.03/1.50      | X2_57 != X0_57
% 8.03/1.50      | X3_57 != X1_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1733]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2524,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X2_57,k10_lattice3(sK3,X2_57,X3_57))
% 8.03/1.50      | X0_57 != X2_57
% 8.03/1.50      | X1_57 != k10_lattice3(sK3,X2_57,X3_57) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2363]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3180,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X1_57,X2_57))
% 8.03/1.50      | ~ r1_orders_2(sK3,X1_57,k10_lattice3(sK3,X1_57,X2_57))
% 8.03/1.50      | X0_57 != X1_57
% 8.03/1.50      | k13_lattice3(sK3,X1_57,X2_57) != k10_lattice3(sK3,X1_57,X2_57) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2524]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_25377,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | X0_57 != sK4
% 8.03/1.50      | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_3180]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_25384,plain,
% 8.03/1.50      ( r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,k10_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5)
% 8.03/1.50      | sK4 != sK4 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_25377]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1725,plain,
% 8.03/1.50      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 8.03/1.50      theory(equality) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_23240,plain,
% 8.03/1.50      ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X0_57
% 8.03/1.50      | sK4 != X0_57
% 8.03/1.50      | sK4 = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1725]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_23241,plain,
% 8.03/1.50      ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4
% 8.03/1.50      | sK4 = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | sK4 != sK4 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_23240]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2352,plain,
% 8.03/1.50      ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X0_57
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4
% 8.03/1.50      | sK4 != X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1725]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14389,plain,
% 8.03/1.50      ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4
% 8.03/1.50      | sK4 != k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2352]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_26,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | v2_struct_0(X0)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 8.03/1.50      inference(cnf_transformation,[],[f96]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14,plain,
% 8.03/1.50      ( ~ v2_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f82]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_251,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_26,c_14]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_252,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | r1_orders_2(X0,sK2(X0,X2,X3,X1),X2)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | k11_lattice3(X0,X2,X3) = X1 ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_251]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1100,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | r1_orders_2(X0,sK2(X0,X3,X2,X1),X3)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_252,c_39]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1101,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | ~ v2_lattice3(sK3)
% 8.03/1.50      | ~ l1_orders_2(sK3)
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1100]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_37,negated_conjecture,
% 8.03/1.50      ( v2_lattice3(sK3) ),
% 8.03/1.50      inference(cnf_transformation,[],[f104]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1103,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_1101,c_37,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1104,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X2)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_1103]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1705,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,X2_57)
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X2_57,X1_57,X0_57),X2_57)
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2_57,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2_57,X1_57) = X0_57 ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1104]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3727,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X2_57,X3_57))
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57),X0_57),X1_57)
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,X2_57,X3_57),u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57)) = X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1705]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14315,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,sK4,sK5),X0_57),X1_57)
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_3727]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14332,plain,
% 8.03/1.50      ( r1_orders_2(sK3,sK2(sK3,sK4,k13_lattice3(sK3,sK4,sK5),sK4),sK4)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,sK4)
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_14315]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_24,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | v2_struct_0(X0)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 8.03/1.50      inference(cnf_transformation,[],[f98]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_263,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_24,c_14]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_264,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | ~ r1_orders_2(X0,sK2(X0,X2,X3,X1),X1)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ v5_orders_2(X0)
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | k11_lattice3(X0,X2,X3) = X1 ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_263]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1034,plain,
% 8.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.03/1.50      | ~ r1_orders_2(X0,sK2(X0,X3,X2,X1),X1)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.03/1.50      | ~ v2_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | k11_lattice3(X0,X3,X2) = X1
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_264,c_39]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1035,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | ~ v2_lattice3(sK3)
% 8.03/1.50      | ~ l1_orders_2(sK3)
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1034]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1039,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_1035,c_37,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1040,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0,X2)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X2,X1,X0),X0)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2,X1) = X0 ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_1039]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1707,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,X2_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X2_57,X1_57,X0_57),X0_57)
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X2_57,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X2_57,X1_57) = X0_57 ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1040]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3725,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,X2_57,X3_57))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57),X0_57),X0_57)
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,X2_57,X3_57),u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,X2_57,X3_57)) = X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1707]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14316,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ r1_orders_2(sK3,X0_57,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK2(sK3,X1_57,k13_lattice3(sK3,sK4,sK5),X0_57),X0_57)
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1_57,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_3725]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_14328,plain,
% 8.03/1.50      ( ~ r1_orders_2(sK3,sK2(sK3,sK4,k13_lattice3(sK3,sK4,sK5),sK4),sK4)
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | ~ r1_orders_2(sK3,sK4,sK4)
% 8.03/1.50      | ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = sK4 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_14316]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_31,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | ~ v5_orders_2(X1)
% 8.03/1.50      | ~ v2_lattice3(X1)
% 8.03/1.50      | ~ l1_orders_2(X1)
% 8.03/1.50      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f99]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1239,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | ~ v2_lattice3(X1)
% 8.03/1.50      | ~ l1_orders_2(X1)
% 8.03/1.50      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 8.03/1.50      | sK3 != X1 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1240,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ v2_lattice3(sK3)
% 8.03/1.50      | ~ l1_orders_2(sK3)
% 8.03/1.50      | k11_lattice3(sK3,X0,X1) = k12_lattice3(sK3,X0,X1) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1239]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1244,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X0,X1) = k12_lattice3(sK3,X0,X1) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_1240,c_37,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1245,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1,X0) = k12_lattice3(sK3,X1,X0) ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_1244]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1700,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,X1_57,X0_57) = k12_lattice3(sK3,X1_57,X0_57) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1245]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_7098,plain,
% 8.03/1.50      ( ~ m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 8.03/1.50      | k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1700]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2476,plain,
% 8.03/1.50      ( X0_57 != X1_57
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != X1_57
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = X0_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1725]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2498,plain,
% 8.03/1.50      ( X0_57 != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = X0_57
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2476]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_7097,plain,
% 8.03/1.50      ( k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k11_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5))
% 8.03/1.50      | k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2498]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1695,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | m1_subset_1(k10_lattice3(sK3,X0_57,X1_57),u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1398]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_5941,plain,
% 8.03/1.50      ( m1_subset_1(k10_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1695]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1727,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,X1_57)
% 8.03/1.50      | m1_subset_1(X2_57,X3_57)
% 8.03/1.50      | X2_57 != X0_57
% 8.03/1.50      | X3_57 != X1_57 ),
% 8.03/1.50      theory(equality) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2482,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,X1_57)
% 8.03/1.50      | m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,sK4,sK5) != X0_57
% 8.03/1.50      | u1_struct_0(sK3) != X1_57 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1727]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3130,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,sK4,sK5) != X0_57
% 8.03/1.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_2482]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_4825,plain,
% 8.03/1.50      ( m1_subset_1(k13_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(k10_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,sK4,sK5) != k10_lattice3(sK3,sK4,sK5)
% 8.03/1.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_3130]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2,plain,
% 8.03/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.03/1.50      inference(cnf_transformation,[],[f70]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1721,plain,
% 8.03/1.50      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2268,plain,
% 8.03/1.50      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_12,plain,
% 8.03/1.50      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 8.03/1.50      | ~ l1_orders_2(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f80]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1354,plain,
% 8.03/1.50      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1355,plain,
% 8.03/1.50      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1354]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1698,plain,
% 8.03/1.50      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1355]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2290,plain,
% 8.03/1.50      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1698]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.03/1.50      | ~ v1_relat_1(X1)
% 8.03/1.50      | v1_relat_1(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f69]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1722,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 8.03/1.50      | ~ v1_relat_1(X1_57)
% 8.03/1.50      | v1_relat_1(X0_57) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2267,plain,
% 8.03/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 8.03/1.50      | v1_relat_1(X1_57) != iProver_top
% 8.03/1.50      | v1_relat_1(X0_57) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2610,plain,
% 8.03/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != iProver_top
% 8.03/1.50      | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
% 8.03/1.50      inference(superposition,[status(thm)],[c_2290,c_2267]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3966,plain,
% 8.03/1.50      ( v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
% 8.03/1.50      inference(superposition,[status(thm)],[c_2268,c_2610]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3967,plain,
% 8.03/1.50      ( v1_relat_1(u1_orders_2(sK3)) ),
% 8.03/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3966]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1724,plain,( X0_57 = X0_57 ),theory(equality) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3113,plain,
% 8.03/1.50      ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) = k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1724]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3084,plain,
% 8.03/1.50      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1724]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_34,negated_conjecture,
% 8.03/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(cnf_transformation,[],[f107]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1716,negated_conjecture,
% 8.03/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_34]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2272,plain,
% 8.03/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1716]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_35,negated_conjecture,
% 8.03/1.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(cnf_transformation,[],[f106]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1715,negated_conjecture,
% 8.03/1.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_35]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2273,plain,
% 8.03/1.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_32,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | ~ v5_orders_2(X1)
% 8.03/1.50      | ~ v1_lattice3(X1)
% 8.03/1.50      | ~ l1_orders_2(X1)
% 8.03/1.50      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f100]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_923,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.03/1.50      | ~ v5_orders_2(X1)
% 8.03/1.50      | ~ l1_orders_2(X1)
% 8.03/1.50      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 8.03/1.50      | sK3 != X1 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_32,c_38]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_924,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ v5_orders_2(sK3)
% 8.03/1.50      | ~ l1_orders_2(sK3)
% 8.03/1.50      | k13_lattice3(sK3,X0,X1) = k10_lattice3(sK3,X0,X1) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_923]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_928,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,X0,X1) = k10_lattice3(sK3,X0,X1) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_924,c_39,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_929,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,X1,X0) = k10_lattice3(sK3,X1,X0) ),
% 8.03/1.50      inference(renaming,[status(thm)],[c_928]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1709,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | k13_lattice3(sK3,X1_57,X0_57) = k10_lattice3(sK3,X1_57,X0_57) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_929]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2279,plain,
% 8.03/1.50      ( k13_lattice3(sK3,X0_57,X1_57) = k10_lattice3(sK3,X0_57,X1_57)
% 8.03/1.50      | m1_subset_1(X1_57,u1_struct_0(sK3)) != iProver_top
% 8.03/1.50      | m1_subset_1(X0_57,u1_struct_0(sK3)) != iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1709]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2490,plain,
% 8.03/1.50      ( k13_lattice3(sK3,sK4,X0_57) = k10_lattice3(sK3,sK4,X0_57)
% 8.03/1.50      | m1_subset_1(X0_57,u1_struct_0(sK3)) != iProver_top ),
% 8.03/1.50      inference(superposition,[status(thm)],[c_2273,c_2279]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3079,plain,
% 8.03/1.50      ( k13_lattice3(sK3,sK4,sK5) = k10_lattice3(sK3,sK4,sK5) ),
% 8.03/1.50      inference(superposition,[status(thm)],[c_2272,c_2490]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_8,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | ~ v3_orders_2(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f75]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_40,negated_conjecture,
% 8.03/1.50      ( v3_orders_2(sK3) ),
% 8.03/1.50      inference(cnf_transformation,[],[f101]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_554,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_40]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_555,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
% 8.03/1.50      | ~ l1_orders_2(sK3) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_554]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_113,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
% 8.03/1.50      | ~ l1_orders_2(sK3)
% 8.03/1.50      | ~ v3_orders_2(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_557,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_555,c_40,c_36,c_113]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1714,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_557]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2274,plain,
% 8.03/1.50      ( r1_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_5,plain,
% 8.03/1.50      ( ~ r1_relat_2(X0,X1)
% 8.03/1.50      | ~ r2_hidden(X2,X1)
% 8.03/1.50      | r2_hidden(k4_tarski(X2,X2),X0)
% 8.03/1.50      | ~ v1_relat_1(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f71]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1718,plain,
% 8.03/1.50      ( ~ r1_relat_2(X0_57,X1_57)
% 8.03/1.50      | ~ r2_hidden(X2_57,X1_57)
% 8.03/1.50      | r2_hidden(k4_tarski(X2_57,X2_57),X0_57)
% 8.03/1.50      | ~ v1_relat_1(X0_57) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_2271,plain,
% 8.03/1.50      ( r1_relat_2(X0_57,X1_57) != iProver_top
% 8.03/1.50      | r2_hidden(X2_57,X1_57) != iProver_top
% 8.03/1.50      | r2_hidden(k4_tarski(X2_57,X2_57),X0_57) = iProver_top
% 8.03/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 8.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1718]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3005,plain,
% 8.03/1.50      ( r2_hidden(X0_57,u1_struct_0(sK3)) != iProver_top
% 8.03/1.50      | r2_hidden(k4_tarski(X0_57,X0_57),u1_orders_2(sK3)) = iProver_top
% 8.03/1.50      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 8.03/1.50      inference(superposition,[status(thm)],[c_2274,c_2271]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3006,plain,
% 8.03/1.50      ( ~ r2_hidden(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | r2_hidden(k4_tarski(X0_57,X0_57),u1_orders_2(sK3))
% 8.03/1.50      | ~ v1_relat_1(u1_orders_2(sK3)) ),
% 8.03/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3005]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_3008,plain,
% 8.03/1.50      ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
% 8.03/1.50      | ~ r2_hidden(sK4,u1_struct_0(sK3))
% 8.03/1.50      | ~ v1_relat_1(u1_orders_2(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_3006]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_9,plain,
% 8.03/1.50      ( r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 8.03/1.50      | ~ l1_orders_2(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f78]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1379,plain,
% 8.03/1.50      ( r1_orders_2(X0,X1,X2)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.03/1.50      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 8.03/1.50      | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_36]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1380,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0,X1)
% 8.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1379]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1696,plain,
% 8.03/1.50      ( r1_orders_2(sK3,X0_57,X1_57)
% 8.03/1.50      | ~ m1_subset_1(X1_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | ~ r2_hidden(k4_tarski(X0_57,X1_57),u1_orders_2(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1380]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1808,plain,
% 8.03/1.50      ( r1_orders_2(sK3,sK4,sK4)
% 8.03/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 8.03/1.50      | ~ r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1696]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_0,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 8.03/1.50      inference(cnf_transformation,[],[f68]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_11,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 8.03/1.50      inference(cnf_transformation,[],[f79]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_6,plain,
% 8.03/1.50      ( v2_struct_0(X0)
% 8.03/1.50      | ~ l1_struct_0(X0)
% 8.03/1.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 8.03/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_513,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0)
% 8.03/1.50      | v2_struct_0(X0)
% 8.03/1.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 8.03/1.50      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_581,plain,
% 8.03/1.50      ( ~ v1_lattice3(X0)
% 8.03/1.50      | ~ l1_orders_2(X0)
% 8.03/1.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 8.03/1.50      inference(resolution,[status(thm)],[c_513,c_13]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_707,plain,
% 8.03/1.50      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_581,c_38]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_708,plain,
% 8.03/1.50      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_707]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_95,plain,
% 8.03/1.50      ( ~ v2_lattice3(sK3) | ~ l1_orders_2(sK3) | ~ v2_struct_0(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_104,plain,
% 8.03/1.50      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_117,plain,
% 8.03/1.50      ( v2_struct_0(sK3)
% 8.03/1.50      | ~ l1_struct_0(sK3)
% 8.03/1.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_710,plain,
% 8.03/1.50      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 8.03/1.50      inference(global_propositional_subsumption,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_708,c_37,c_36,c_95,c_104,c_117]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1341,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,X1)
% 8.03/1.50      | r2_hidden(X0,X1)
% 8.03/1.50      | u1_struct_0(sK3) != X1 ),
% 8.03/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_710]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1342,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 8.03/1.50      | r2_hidden(X0,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(unflattening,[status(thm)],[c_1341]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1708,plain,
% 8.03/1.50      ( ~ m1_subset_1(X0_57,u1_struct_0(sK3))
% 8.03/1.50      | r2_hidden(X0_57,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_1342]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1778,plain,
% 8.03/1.50      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 8.03/1.50      | r2_hidden(sK4,u1_struct_0(sK3)) ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1708]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_33,negated_conjecture,
% 8.03/1.50      ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 ),
% 8.03/1.50      inference(cnf_transformation,[],[f108]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1717,negated_conjecture,
% 8.03/1.50      ( k12_lattice3(sK3,sK4,k13_lattice3(sK3,sK4,sK5)) != sK4 ),
% 8.03/1.50      inference(subtyping,[status(esa)],[c_33]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(c_1747,plain,
% 8.03/1.50      ( sK4 = sK4 ),
% 8.03/1.50      inference(instantiation,[status(thm)],[c_1724]) ).
% 8.03/1.50  
% 8.03/1.50  cnf(contradiction,plain,
% 8.03/1.50      ( $false ),
% 8.03/1.50      inference(minisat,
% 8.03/1.50                [status(thm)],
% 8.03/1.50                [c_25749,c_25384,c_23241,c_14389,c_14332,c_14328,c_7098,
% 8.03/1.50                 c_7097,c_5941,c_4825,c_3967,c_3113,c_3084,c_3079,c_3008,
% 8.03/1.50                 c_1808,c_1778,c_1717,c_1747,c_34,c_35]) ).
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.50  
% 8.03/1.50  ------                               Statistics
% 8.03/1.50  
% 8.03/1.50  ------ General
% 8.03/1.50  
% 8.03/1.50  abstr_ref_over_cycles:                  0
% 8.03/1.50  abstr_ref_under_cycles:                 0
% 8.03/1.50  gc_basic_clause_elim:                   0
% 8.03/1.50  forced_gc_time:                         0
% 8.03/1.50  parsing_time:                           0.011
% 8.03/1.50  unif_index_cands_time:                  0.
% 8.03/1.50  unif_index_add_time:                    0.
% 8.03/1.50  orderings_time:                         0.
% 8.03/1.50  out_proof_time:                         0.014
% 8.03/1.50  total_time:                             0.988
% 8.03/1.50  num_of_symbols:                         61
% 8.03/1.50  num_of_terms:                           38005
% 8.03/1.50  
% 8.03/1.50  ------ Preprocessing
% 8.03/1.50  
% 8.03/1.50  num_of_splits:                          0
% 8.03/1.50  num_of_split_atoms:                     0
% 8.03/1.50  num_of_reused_defs:                     0
% 8.03/1.50  num_eq_ax_congr_red:                    53
% 8.03/1.50  num_of_sem_filtered_clauses:            1
% 8.03/1.50  num_of_subtypes:                        2
% 8.03/1.50  monotx_restored_types:                  0
% 8.03/1.50  sat_num_of_epr_types:                   0
% 8.03/1.50  sat_num_of_non_cyclic_types:            0
% 8.03/1.50  sat_guarded_non_collapsed_types:        1
% 8.03/1.50  num_pure_diseq_elim:                    0
% 8.03/1.50  simp_replaced_by:                       0
% 8.03/1.50  res_preprocessed:                       159
% 8.03/1.50  prep_upred:                             0
% 8.03/1.50  prep_unflattend:                        34
% 8.03/1.50  smt_new_axioms:                         0
% 8.03/1.50  pred_elim_cands:                        5
% 8.03/1.50  pred_elim:                              8
% 8.03/1.50  pred_elim_cl:                           10
% 8.03/1.50  pred_elim_cycles:                       14
% 8.03/1.50  merged_defs:                            0
% 8.03/1.50  merged_defs_ncl:                        0
% 8.03/1.50  bin_hyper_res:                          0
% 8.03/1.50  prep_cycles:                            4
% 8.03/1.50  pred_elim_time:                         0.013
% 8.03/1.50  splitting_time:                         0.
% 8.03/1.50  sem_filter_time:                        0.
% 8.03/1.50  monotx_time:                            0.
% 8.03/1.50  subtype_inf_time:                       0.
% 8.03/1.50  
% 8.03/1.50  ------ Problem properties
% 8.03/1.50  
% 8.03/1.50  clauses:                                31
% 8.03/1.50  conjectures:                            3
% 8.03/1.50  epr:                                    0
% 8.03/1.50  horn:                                   24
% 8.03/1.50  ground:                                 5
% 8.03/1.50  unary:                                  6
% 8.03/1.50  binary:                                 1
% 8.03/1.50  lits:                                   124
% 8.03/1.50  lits_eq:                                12
% 8.03/1.50  fd_pure:                                0
% 8.03/1.50  fd_pseudo:                              0
% 8.03/1.50  fd_cond:                                0
% 8.03/1.50  fd_pseudo_cond:                         8
% 8.03/1.50  ac_symbols:                             0
% 8.03/1.50  
% 8.03/1.50  ------ Propositional Solver
% 8.03/1.50  
% 8.03/1.50  prop_solver_calls:                      28
% 8.03/1.50  prop_fast_solver_calls:                 2230
% 8.03/1.50  smt_solver_calls:                       0
% 8.03/1.50  smt_fast_solver_calls:                  0
% 8.03/1.50  prop_num_of_clauses:                    9073
% 8.03/1.50  prop_preprocess_simplified:             25640
% 8.03/1.50  prop_fo_subsumed:                       69
% 8.03/1.50  prop_solver_time:                       0.
% 8.03/1.50  smt_solver_time:                        0.
% 8.03/1.50  smt_fast_solver_time:                   0.
% 8.03/1.50  prop_fast_solver_time:                  0.
% 8.03/1.50  prop_unsat_core_time:                   0.001
% 8.03/1.50  
% 8.03/1.50  ------ QBF
% 8.03/1.50  
% 8.03/1.50  qbf_q_res:                              0
% 8.03/1.50  qbf_num_tautologies:                    0
% 8.03/1.50  qbf_prep_cycles:                        0
% 8.03/1.50  
% 8.03/1.50  ------ BMC1
% 8.03/1.50  
% 8.03/1.50  bmc1_current_bound:                     -1
% 8.03/1.50  bmc1_last_solved_bound:                 -1
% 8.03/1.50  bmc1_unsat_core_size:                   -1
% 8.03/1.50  bmc1_unsat_core_parents_size:           -1
% 8.03/1.50  bmc1_merge_next_fun:                    0
% 8.03/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.03/1.50  
% 8.03/1.50  ------ Instantiation
% 8.03/1.50  
% 8.03/1.50  inst_num_of_clauses:                    2582
% 8.03/1.50  inst_num_in_passive:                    1442
% 8.03/1.50  inst_num_in_active:                     788
% 8.03/1.50  inst_num_in_unprocessed:                351
% 8.03/1.50  inst_num_of_loops:                      1017
% 8.03/1.50  inst_num_of_learning_restarts:          0
% 8.03/1.50  inst_num_moves_active_passive:          227
% 8.03/1.50  inst_lit_activity:                      0
% 8.03/1.50  inst_lit_activity_moves:                0
% 8.03/1.50  inst_num_tautologies:                   0
% 8.03/1.50  inst_num_prop_implied:                  0
% 8.03/1.50  inst_num_existing_simplified:           0
% 8.03/1.50  inst_num_eq_res_simplified:             0
% 8.03/1.50  inst_num_child_elim:                    0
% 8.03/1.50  inst_num_of_dismatching_blockings:      3175
% 8.03/1.50  inst_num_of_non_proper_insts:           2304
% 8.03/1.50  inst_num_of_duplicates:                 0
% 8.03/1.50  inst_inst_num_from_inst_to_res:         0
% 8.03/1.50  inst_dismatching_checking_time:         0.
% 8.03/1.50  
% 8.03/1.50  ------ Resolution
% 8.03/1.50  
% 8.03/1.50  res_num_of_clauses:                     0
% 8.03/1.50  res_num_in_passive:                     0
% 8.03/1.50  res_num_in_active:                      0
% 8.03/1.50  res_num_of_loops:                       163
% 8.03/1.50  res_forward_subset_subsumed:            44
% 8.03/1.50  res_backward_subset_subsumed:           0
% 8.03/1.50  res_forward_subsumed:                   0
% 8.03/1.50  res_backward_subsumed:                  0
% 8.03/1.50  res_forward_subsumption_resolution:     0
% 8.03/1.50  res_backward_subsumption_resolution:    3
% 8.03/1.50  res_clause_to_clause_subsumption:       2994
% 8.03/1.50  res_orphan_elimination:                 0
% 8.03/1.50  res_tautology_del:                      45
% 8.03/1.50  res_num_eq_res_simplified:              0
% 8.03/1.50  res_num_sel_changes:                    0
% 8.03/1.50  res_moves_from_active_to_pass:          0
% 8.03/1.50  
% 8.03/1.50  ------ Superposition
% 8.03/1.50  
% 8.03/1.50  sup_time_total:                         0.
% 8.03/1.50  sup_time_generating:                    0.
% 8.03/1.50  sup_time_sim_full:                      0.
% 8.03/1.50  sup_time_sim_immed:                     0.
% 8.03/1.50  
% 8.03/1.50  sup_num_of_clauses:                     467
% 8.03/1.50  sup_num_in_active:                      175
% 8.03/1.50  sup_num_in_passive:                     292
% 8.03/1.50  sup_num_of_loops:                       202
% 8.03/1.50  sup_fw_superposition:                   420
% 8.03/1.50  sup_bw_superposition:                   121
% 8.03/1.50  sup_immediate_simplified:               119
% 8.03/1.50  sup_given_eliminated:                   0
% 8.03/1.50  comparisons_done:                       0
% 8.03/1.50  comparisons_avoided:                    0
% 8.03/1.50  
% 8.03/1.50  ------ Simplifications
% 8.03/1.50  
% 8.03/1.50  
% 8.03/1.50  sim_fw_subset_subsumed:                 7
% 8.03/1.50  sim_bw_subset_subsumed:                 0
% 8.03/1.50  sim_fw_subsumed:                        0
% 8.03/1.50  sim_bw_subsumed:                        1
% 8.03/1.50  sim_fw_subsumption_res:                 0
% 8.03/1.50  sim_bw_subsumption_res:                 0
% 8.03/1.50  sim_tautology_del:                      5
% 8.03/1.50  sim_eq_tautology_del:                   28
% 8.03/1.50  sim_eq_res_simp:                        0
% 8.03/1.50  sim_fw_demodulated:                     0
% 8.03/1.50  sim_bw_demodulated:                     26
% 8.03/1.50  sim_light_normalised:                   114
% 8.03/1.50  sim_joinable_taut:                      0
% 8.03/1.50  sim_joinable_simp:                      0
% 8.03/1.50  sim_ac_normalised:                      0
% 8.03/1.50  sim_smt_subsumption:                    0
% 8.03/1.50  
%------------------------------------------------------------------------------
