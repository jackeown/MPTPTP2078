%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:02 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 571 expanded)
%              Number of clauses        :  103 ( 153 expanded)
%              Number of leaves         :   17 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          :  924 (3710 expanded)
%              Number of equality atoms :  180 ( 618 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,k12_lattice3(X0,X1,sK4),sK4) != sK4
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k13_lattice3(X0,k12_lattice3(X0,sK3,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK2,k12_lattice3(sK2,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f41,f40,f39])).

fof(f69,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1134,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1501,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1133,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1502,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_26,c_23])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_902])).

cnf(c_1516,plain,
    ( k11_lattice3(sK2,X0_47,X1_47) = k12_lattice3(sK2,X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_2242,plain,
    ( k11_lattice3(sK2,sK3,X0_47) = k12_lattice3(sK2,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1516])).

cnf(c_2383,plain,
    ( k11_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1501,c_2242])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_16,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_553,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_554,plain,
    ( ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_82,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_556,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_25,c_23,c_82])).

cnf(c_665,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_556])).

cnf(c_666,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_668,plain,
    ( ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_26,c_24,c_23])).

cnf(c_669,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_964,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_947,c_669])).

cnf(c_1116,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_964])).

cnf(c_1519,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X1_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_9604,plain,
    ( r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2383,c_1519])).

cnf(c_2241,plain,
    ( k11_lattice3(sK2,sK4,X0_47) = k12_lattice3(sK2,sK4,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1516])).

cnf(c_2259,plain,
    ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1502,c_2241])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_947])).

cnf(c_1518,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_2533,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_1518])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X0_48)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1814,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(X1_47,u1_struct_0(sK2))
    | X1_47 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1899,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_2031,plain,
    ( ~ m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,sK4) != k12_lattice3(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_2032,plain,
    ( k12_lattice3(sK2,sK3,sK4) != k12_lattice3(sK2,sK4,sK3)
    | m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_196,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_1])).

cnf(c_197,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_348,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_197,c_25])).

cnf(c_349,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_353,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_26,c_23])).

cnf(c_354,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_1131,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X2_47,X1_47)
    | ~ r1_orders_2(sK2,X1_47,sK0(sK2,X0_47,X2_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1925,plain,
    ( ~ r1_orders_2(sK2,X0_47,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47))
    | ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47)
    | ~ r1_orders_2(sK2,sK4,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1941,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47
    | r1_orders_2(sK2,X0_47,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47)) != iProver_top
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47) != iProver_top
    | r1_orders_2(sK2,sK4,X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_1943,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) != iProver_top
    | r1_orders_2(sK2,sK4,sK4) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_191,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_1])).

cnf(c_192,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_381,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_192,c_25])).

cnf(c_382,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_386,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_26,c_23])).

cnf(c_387,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_1130,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X2_47,X1_47)
    | r1_orders_2(sK2,X2_47,sK0(sK2,X0_47,X2_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_47,X2_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_1926,plain,
    ( ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47)
    | ~ r1_orders_2(sK2,sK4,X0_47)
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1937,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47) != iProver_top
    | r1_orders_2(sK2,sK4,X0_47) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_1939,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) = iProver_top
    | r1_orders_2(sK2,sK4,sK4) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k12_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_26,c_23])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X0,X1) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_1118,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_923])).

cnf(c_1886,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1138,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1833,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_47
    | sK4 != X0_47
    | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1834,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
    | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_26,c_23])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_569])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1_47,X0_47) = k10_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1794,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1782,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_47
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | sK4 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1792,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | sK4 != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_328,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_25,c_23,c_82])).

cnf(c_1132,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1151,plain,
    ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_1153,plain,
    ( r1_orders_2(sK2,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_20,negated_conjecture,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1135,negated_conjecture,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1137,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1148,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9604,c_2533,c_2032,c_1943,c_1939,c_1886,c_1834,c_1794,c_1792,c_1153,c_1135,c_1148,c_34,c_21,c_33,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:26:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.25/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.99  
% 3.25/0.99  ------  iProver source info
% 3.25/0.99  
% 3.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.99  git: non_committed_changes: false
% 3.25/0.99  git: last_make_outside_of_git: false
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     num_symb
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       true
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  ------ Parsing...
% 3.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.99  ------ Proving...
% 3.25/0.99  ------ Problem Properties 
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  clauses                                 22
% 3.25/0.99  conjectures                             3
% 3.25/0.99  EPR                                     0
% 3.25/0.99  Horn                                    16
% 3.25/0.99  unary                                   3
% 3.25/0.99  binary                                  1
% 3.25/0.99  lits                                    100
% 3.25/0.99  lits eq                                 12
% 3.25/0.99  fd_pure                                 0
% 3.25/0.99  fd_pseudo                               0
% 3.25/0.99  fd_cond                                 0
% 3.25/0.99  fd_pseudo_cond                          8
% 3.25/0.99  AC symbols                              0
% 3.25/0.99  
% 3.25/0.99  ------ Schedule dynamic 5 is on 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  Current options:
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     none
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       false
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ Proving...
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS status Theorem for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  fof(f9,conjecture,(
% 3.25/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f10,negated_conjecture,(
% 3.25/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 3.25/0.99    inference(negated_conjecture,[],[f9])).
% 3.25/0.99  
% 3.25/0.99  fof(f27,plain,(
% 3.25/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f10])).
% 3.25/0.99  
% 3.25/0.99  fof(f28,plain,(
% 3.25/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f27])).
% 3.25/0.99  
% 3.25/0.99  fof(f41,plain,(
% 3.25/0.99    ( ! [X0,X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k13_lattice3(X0,k12_lattice3(X0,X1,sK4),sK4) != sK4 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f40,plain,(
% 3.25/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,sK3,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f39,plain,(
% 3.25/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK2,k12_lattice3(sK2,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f42,plain,(
% 3.25/0.99    ((k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f41,f40,f39])).
% 3.25/0.99  
% 3.25/0.99  fof(f69,plain,(
% 3.25/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f68,plain,(
% 3.25/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f7,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f23,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f7])).
% 3.25/0.99  
% 3.25/0.99  fof(f24,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f23])).
% 3.25/0.99  
% 3.25/0.99  fof(f61,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f24])).
% 3.25/0.99  
% 3.25/0.99  fof(f66,plain,(
% 3.25/0.99    v2_lattice3(sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f64,plain,(
% 3.25/0.99    v5_orders_2(sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f67,plain,(
% 3.25/0.99    l1_orders_2(sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f4,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f17,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f4])).
% 3.25/0.99  
% 3.25/0.99  fof(f18,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f17])).
% 3.25/0.99  
% 3.25/0.99  fof(f46,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f18])).
% 3.25/0.99  
% 3.25/0.99  fof(f6,axiom,(
% 3.25/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f21,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f6])).
% 3.25/0.99  
% 3.25/0.99  fof(f22,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(flattening,[],[f21])).
% 3.25/0.99  
% 3.25/0.99  fof(f34,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(nnf_transformation,[],[f22])).
% 3.25/0.99  
% 3.25/0.99  fof(f35,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(flattening,[],[f34])).
% 3.25/0.99  
% 3.25/0.99  fof(f36,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(rectify,[],[f35])).
% 3.25/0.99  
% 3.25/0.99  fof(f37,plain,(
% 3.25/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f38,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f55,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f38])).
% 3.25/0.99  
% 3.25/0.99  fof(f75,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.25/0.99    inference(equality_resolution,[],[f55])).
% 3.25/0.99  
% 3.25/0.99  fof(f2,axiom,(
% 3.25/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f13,plain,(
% 3.25/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.25/0.99    inference(ennf_transformation,[],[f2])).
% 3.25/0.99  
% 3.25/0.99  fof(f14,plain,(
% 3.25/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f13])).
% 3.25/0.99  
% 3.25/0.99  fof(f44,plain,(
% 3.25/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f14])).
% 3.25/0.99  
% 3.25/0.99  fof(f65,plain,(
% 3.25/0.99    v1_lattice3(sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f5,axiom,(
% 3.25/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f19,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f5])).
% 3.25/0.99  
% 3.25/0.99  fof(f20,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(flattening,[],[f19])).
% 3.25/0.99  
% 3.25/0.99  fof(f29,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(nnf_transformation,[],[f20])).
% 3.25/0.99  
% 3.25/0.99  fof(f30,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(flattening,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  fof(f31,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(rectify,[],[f30])).
% 3.25/0.99  
% 3.25/0.99  fof(f32,plain,(
% 3.25/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f33,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.25/0.99  
% 3.25/0.99  fof(f53,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f33])).
% 3.25/0.99  
% 3.25/0.99  fof(f52,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f33])).
% 3.25/0.99  
% 3.25/0.99  fof(f3,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f15,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f3])).
% 3.25/0.99  
% 3.25/0.99  fof(f16,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f15])).
% 3.25/0.99  
% 3.25/0.99  fof(f45,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f16])).
% 3.25/0.99  
% 3.25/0.99  fof(f8,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f25,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f8])).
% 3.25/0.99  
% 3.25/0.99  fof(f26,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.25/0.99    inference(flattening,[],[f25])).
% 3.25/0.99  
% 3.25/0.99  fof(f62,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f1,axiom,(
% 3.25/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 3.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f11,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.25/0.99    inference(ennf_transformation,[],[f1])).
% 3.25/0.99  
% 3.25/0.99  fof(f12,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.25/0.99    inference(flattening,[],[f11])).
% 3.25/0.99  
% 3.25/0.99  fof(f43,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f12])).
% 3.25/0.99  
% 3.25/0.99  fof(f63,plain,(
% 3.25/0.99    v3_orders_2(sK2)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f70,plain,(
% 3.25/0.99    k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  cnf(c_21,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1134,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1501,plain,
% 3.25/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_22,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1133,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1502,plain,
% 3.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_18,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ v2_lattice3(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_24,negated_conjecture,
% 3.25/0.99      ( v2_lattice3(sK2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_896,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
% 3.25/0.99      | sK2 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_897,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2)
% 3.25/0.99      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_896]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_26,negated_conjecture,
% 3.25/0.99      ( v5_orders_2(sK2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_23,negated_conjecture,
% 3.25/0.99      ( l1_orders_2(sK2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_901,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_897,c_26,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_902,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_901]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1119,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | k11_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X1_47,X0_47) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_902]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1516,plain,
% 3.25/0.99      ( k11_lattice3(sK2,X0_47,X1_47) = k12_lattice3(sK2,X0_47,X1_47)
% 3.25/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2242,plain,
% 3.25/0.99      ( k11_lattice3(sK2,sK3,X0_47) = k12_lattice3(sK2,sK3,X0_47)
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1502,c_1516]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2383,plain,
% 3.25/0.99      ( k11_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK3,sK4) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1501,c_2242]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
% 3.25/0.99      | ~ l1_orders_2(X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_946,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
% 3.25/0.99      | sK2 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_947,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_946]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_16,plain,
% 3.25/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v2_lattice3(X0)
% 3.25/0.99      | v2_struct_0(X0)
% 3.25/0.99      | ~ l1_orders_2(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1,plain,
% 3.25/0.99      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_25,negated_conjecture,
% 3.25/0.99      ( v1_lattice3(sK2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_553,plain,
% 3.25/0.99      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK2 != X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_25]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_554,plain,
% 3.25/0.99      ( ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_553]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_82,plain,
% 3.25/0.99      ( ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_556,plain,
% 3.25/0.99      ( ~ v2_struct_0(sK2) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_554,c_25,c_23,c_82]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_665,plain,
% 3.25/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v2_lattice3(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | sK2 != X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_556]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_666,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ v2_lattice3(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_665]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_668,plain,
% 3.25/0.99      ( ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_666,c_26,c_24,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_669,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_668]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_964,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X1)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(backward_subsumption_resolution,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_947,c_669]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1116,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X1_47)
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_964]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1519,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X1_47) = iProver_top
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9604,plain,
% 3.25/0.99      ( r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_2383,c_1519]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2241,plain,
% 3.25/0.99      ( k11_lattice3(sK2,sK4,X0_47) = k12_lattice3(sK2,sK4,X0_47)
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1501,c_1516]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2259,plain,
% 3.25/0.99      ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK4,sK3) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1502,c_2241]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1117,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_947]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1518,plain,
% 3.25/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2533,plain,
% 3.25/0.99      ( m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2)) = iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_2259,c_1518]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1140,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,X0_48)
% 3.25/0.99      | m1_subset_1(X1_47,X0_48)
% 3.25/0.99      | X1_47 != X0_47 ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1814,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | X1_47 != X0_47 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1140]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1899,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,sK3,sK4) != X0_47 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1814]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2031,plain,
% 3.25/0.99      ( ~ m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2))
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,sK3,sK4) != k12_lattice3(sK2,sK4,sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1899]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2032,plain,
% 3.25/0.99      ( k12_lattice3(sK2,sK3,sK4) != k12_lattice3(sK2,sK4,sK3)
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK4,sK3),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v1_lattice3(X0)
% 3.25/0.99      | v2_struct_0(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_196,plain,
% 3.25/0.99      ( ~ v1_lattice3(X0)
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4,c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_197,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v1_lattice3(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_196]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_348,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.25/0.99      | sK2 != X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_197,c_25]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_349,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2)
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_348]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_353,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_349,c_26,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_354,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_353]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1131,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2_47,X1_47)
% 3.25/0.99      | ~ r1_orders_2(sK2,X1_47,sK0(sK2,X0_47,X2_47,X1_47))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0_47,X2_47) = X1_47 ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_354]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1925,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0_47,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47))
% 3.25/0.99      | ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47)
% 3.25/0.99      | ~ r1_orders_2(sK2,sK4,X0_47)
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1131]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1941,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47
% 3.25/0.99      | r1_orders_2(sK2,X0_47,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47)) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,X0_47) != iProver_top
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1943,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 3.25/0.99      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK4) != iProver_top
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1941]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v1_lattice3(X0)
% 3.25/0.99      | v2_struct_0(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_191,plain,
% 3.25/0.99      ( ~ v1_lattice3(X0)
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5,c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_192,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ v1_lattice3(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2 ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_191]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_381,plain,
% 3.25/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.25/0.99      | ~ r1_orders_2(X0,X3,X2)
% 3.25/0.99      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.25/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.25/0.99      | ~ v5_orders_2(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | k10_lattice3(X0,X3,X1) = X2
% 3.25/0.99      | sK2 != X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_192,c_25]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_382,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2)
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_386,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_382,c_26,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_387,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2,X1)
% 3.25/0.99      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0,X2) = X1 ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_386]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1130,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 3.25/0.99      | ~ r1_orders_2(sK2,X2_47,X1_47)
% 3.25/0.99      | r1_orders_2(sK2,X2_47,sK0(sK2,X0_47,X2_47,X1_47))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,X0_47,X2_47) = X1_47 ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_387]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1926,plain,
% 3.25/0.99      ( ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47)
% 3.25/0.99      | ~ r1_orders_2(sK2,sK4,X0_47)
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47))
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.25/0.99      | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1130]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1937,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_47
% 3.25/0.99      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_47) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,X0_47) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_47)) = iProver_top
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1939,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 3.25/0.99      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) = iProver_top
% 3.25/0.99      | r1_orders_2(sK2,sK4,sK4) != iProver_top
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ v2_lattice3(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k12_lattice3(X1,X2,X0) = k12_lattice3(X1,X0,X2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_917,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k12_lattice3(X1,X0,X2) = k12_lattice3(X1,X2,X0)
% 3.25/0.99      | sK2 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_918,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2)
% 3.25/0.99      | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_917]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_922,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_918,c_26,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_923,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X0,X1) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_922]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1118,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X0_47,X1_47) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_923]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1886,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.25/0.99      | k12_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK4,sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1138,plain,
% 3.25/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1833,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_47
% 3.25/0.99      | sK4 != X0_47
% 3.25/0.99      | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1138]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1834,plain,
% 3.25/0.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
% 3.25/0.99      | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 3.25/0.99      | sK4 != sK4 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1833]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_19,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ v1_lattice3(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_564,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.25/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.25/0.99      | ~ v5_orders_2(X1)
% 3.25/0.99      | ~ l1_orders_2(X1)
% 3.25/0.99      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
% 3.25/0.99      | sK2 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_565,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | ~ v5_orders_2(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2)
% 3.25/0.99      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_564]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_569,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_565,c_26,c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_570,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.25/0.99      | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_569]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1124,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.25/0.99      | k13_lattice3(sK2,X1_47,X0_47) = k10_lattice3(sK2,X1_47,X0_47) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_570]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1793,plain,
% 3.25/0.99      ( ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 3.25/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.25/0.99      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1124]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1794,plain,
% 3.25/0.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 3.25/0.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1782,plain,
% 3.25/0.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_47
% 3.25/0.99      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 3.25/0.99      | sK4 != X0_47 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1138]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1792,plain,
% 3.25/0.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 3.25/0.99      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 3.25/0.99      | sK4 != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1782]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_0,plain,
% 3.25/0.99      ( r1_orders_2(X0,X1,X1)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | v2_struct_0(X0)
% 3.25/0.99      | ~ v3_orders_2(X0)
% 3.25/0.99      | ~ l1_orders_2(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_27,negated_conjecture,
% 3.25/0.99      ( v3_orders_2(sK2) ),
% 3.25/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_327,plain,
% 3.25/0.99      ( r1_orders_2(X0,X1,X1)
% 3.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.25/0.99      | v2_struct_0(X0)
% 3.25/0.99      | ~ l1_orders_2(X0)
% 3.25/0.99      | sK2 != X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_328,plain,
% 3.25/0.99      ( r1_orders_2(sK2,X0,X0)
% 3.25/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.25/0.99      | v2_struct_0(sK2)
% 3.25/0.99      | ~ l1_orders_2(sK2) ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_327]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_332,plain,
% 3.25/0.99      ( r1_orders_2(sK2,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_328,c_25,c_23,c_82]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1132,plain,
% 3.25/0.99      ( r1_orders_2(sK2,X0_47,X0_47)
% 3.25/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_332]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1151,plain,
% 3.25/0.99      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 3.25/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1153,plain,
% 3.25/0.99      ( r1_orders_2(sK2,sK4,sK4) = iProver_top
% 3.25/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1151]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_20,negated_conjecture,
% 3.25/0.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
% 3.25/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1135,negated_conjecture,
% 3.25/0.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
% 3.25/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1137,plain,( X0_47 = X0_47 ),theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1148,plain,
% 3.25/0.99      ( sK4 = sK4 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_1137]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_34,plain,
% 3.25/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_33,plain,
% 3.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(contradiction,plain,
% 3.25/0.99      ( $false ),
% 3.25/0.99      inference(minisat,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_9604,c_2533,c_2032,c_1943,c_1939,c_1886,c_1834,c_1794,
% 3.25/0.99                 c_1792,c_1153,c_1135,c_1148,c_34,c_21,c_33,c_22]) ).
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  ------                               Statistics
% 3.25/0.99  
% 3.25/0.99  ------ General
% 3.25/0.99  
% 3.25/0.99  abstr_ref_over_cycles:                  0
% 3.25/0.99  abstr_ref_under_cycles:                 0
% 3.25/0.99  gc_basic_clause_elim:                   0
% 3.25/0.99  forced_gc_time:                         0
% 3.25/0.99  parsing_time:                           0.012
% 3.25/0.99  unif_index_cands_time:                  0.
% 3.25/0.99  unif_index_add_time:                    0.
% 3.25/0.99  orderings_time:                         0.
% 3.25/0.99  out_proof_time:                         0.012
% 3.25/0.99  total_time:                             0.326
% 3.25/0.99  num_of_symbols:                         49
% 3.25/0.99  num_of_terms:                           9763
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing
% 3.25/0.99  
% 3.25/0.99  num_of_splits:                          0
% 3.25/0.99  num_of_split_atoms:                     0
% 3.25/0.99  num_of_reused_defs:                     0
% 3.25/0.99  num_eq_ax_congr_red:                    45
% 3.25/0.99  num_of_sem_filtered_clauses:            1
% 3.25/0.99  num_of_subtypes:                        3
% 3.25/0.99  monotx_restored_types:                  0
% 3.25/0.99  sat_num_of_epr_types:                   0
% 3.25/0.99  sat_num_of_non_cyclic_types:            0
% 3.25/0.99  sat_guarded_non_collapsed_types:        1
% 3.25/0.99  num_pure_diseq_elim:                    0
% 3.25/0.99  simp_replaced_by:                       0
% 3.25/0.99  res_preprocessed:                       107
% 3.25/0.99  prep_upred:                             0
% 3.25/0.99  prep_unflattend:                        20
% 3.25/0.99  smt_new_axioms:                         0
% 3.25/0.99  pred_elim_cands:                        2
% 3.25/0.99  pred_elim:                              6
% 3.25/0.99  pred_elim_cl:                           6
% 3.25/0.99  pred_elim_cycles:                       8
% 3.25/0.99  merged_defs:                            0
% 3.25/0.99  merged_defs_ncl:                        0
% 3.25/0.99  bin_hyper_res:                          0
% 3.25/0.99  prep_cycles:                            4
% 3.25/0.99  pred_elim_time:                         0.029
% 3.25/0.99  splitting_time:                         0.
% 3.25/0.99  sem_filter_time:                        0.
% 3.25/0.99  monotx_time:                            0.
% 3.25/0.99  subtype_inf_time:                       0.
% 3.25/0.99  
% 3.25/0.99  ------ Problem properties
% 3.25/0.99  
% 3.25/0.99  clauses:                                22
% 3.25/0.99  conjectures:                            3
% 3.25/0.99  epr:                                    0
% 3.25/0.99  horn:                                   16
% 3.25/0.99  ground:                                 3
% 3.25/0.99  unary:                                  3
% 3.25/0.99  binary:                                 1
% 3.25/0.99  lits:                                   100
% 3.25/0.99  lits_eq:                                12
% 3.25/0.99  fd_pure:                                0
% 3.25/0.99  fd_pseudo:                              0
% 3.25/0.99  fd_cond:                                0
% 3.25/0.99  fd_pseudo_cond:                         8
% 3.25/0.99  ac_symbols:                             0
% 3.25/0.99  
% 3.25/0.99  ------ Propositional Solver
% 3.25/0.99  
% 3.25/0.99  prop_solver_calls:                      29
% 3.25/0.99  prop_fast_solver_calls:                 1529
% 3.25/0.99  smt_solver_calls:                       0
% 3.25/0.99  smt_fast_solver_calls:                  0
% 3.25/0.99  prop_num_of_clauses:                    3118
% 3.25/0.99  prop_preprocess_simplified:             7427
% 3.25/0.99  prop_fo_subsumed:                       55
% 3.25/0.99  prop_solver_time:                       0.
% 3.25/0.99  smt_solver_time:                        0.
% 3.25/0.99  smt_fast_solver_time:                   0.
% 3.25/0.99  prop_fast_solver_time:                  0.
% 3.25/0.99  prop_unsat_core_time:                   0.
% 3.25/0.99  
% 3.25/0.99  ------ QBF
% 3.25/0.99  
% 3.25/0.99  qbf_q_res:                              0
% 3.25/0.99  qbf_num_tautologies:                    0
% 3.25/0.99  qbf_prep_cycles:                        0
% 3.25/0.99  
% 3.25/0.99  ------ BMC1
% 3.25/0.99  
% 3.25/0.99  bmc1_current_bound:                     -1
% 3.25/0.99  bmc1_last_solved_bound:                 -1
% 3.25/0.99  bmc1_unsat_core_size:                   -1
% 3.25/0.99  bmc1_unsat_core_parents_size:           -1
% 3.25/0.99  bmc1_merge_next_fun:                    0
% 3.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation
% 3.25/0.99  
% 3.25/0.99  inst_num_of_clauses:                    899
% 3.25/0.99  inst_num_in_passive:                    63
% 3.25/0.99  inst_num_in_active:                     445
% 3.25/0.99  inst_num_in_unprocessed:                391
% 3.25/0.99  inst_num_of_loops:                      470
% 3.25/0.99  inst_num_of_learning_restarts:          0
% 3.25/0.99  inst_num_moves_active_passive:          21
% 3.25/0.99  inst_lit_activity:                      0
% 3.25/0.99  inst_lit_activity_moves:                0
% 3.25/0.99  inst_num_tautologies:                   0
% 3.25/0.99  inst_num_prop_implied:                  0
% 3.25/0.99  inst_num_existing_simplified:           0
% 3.25/0.99  inst_num_eq_res_simplified:             0
% 3.25/0.99  inst_num_child_elim:                    0
% 3.25/0.99  inst_num_of_dismatching_blockings:      303
% 3.25/0.99  inst_num_of_non_proper_insts:           1038
% 3.25/0.99  inst_num_of_duplicates:                 0
% 3.25/0.99  inst_inst_num_from_inst_to_res:         0
% 3.25/0.99  inst_dismatching_checking_time:         0.
% 3.25/0.99  
% 3.25/0.99  ------ Resolution
% 3.25/0.99  
% 3.25/0.99  res_num_of_clauses:                     0
% 3.25/0.99  res_num_in_passive:                     0
% 3.25/0.99  res_num_in_active:                      0
% 3.25/0.99  res_num_of_loops:                       111
% 3.25/0.99  res_forward_subset_subsumed:            98
% 3.25/0.99  res_backward_subset_subsumed:           2
% 3.25/0.99  res_forward_subsumed:                   0
% 3.25/0.99  res_backward_subsumed:                  0
% 3.25/0.99  res_forward_subsumption_resolution:     0
% 3.25/0.99  res_backward_subsumption_resolution:    3
% 3.25/0.99  res_clause_to_clause_subsumption:       1229
% 3.25/0.99  res_orphan_elimination:                 0
% 3.25/0.99  res_tautology_del:                      111
% 3.25/0.99  res_num_eq_res_simplified:              0
% 3.25/0.99  res_num_sel_changes:                    0
% 3.25/0.99  res_moves_from_active_to_pass:          0
% 3.25/0.99  
% 3.25/0.99  ------ Superposition
% 3.25/0.99  
% 3.25/0.99  sup_time_total:                         0.
% 3.25/0.99  sup_time_generating:                    0.
% 3.25/0.99  sup_time_sim_full:                      0.
% 3.25/0.99  sup_time_sim_immed:                     0.
% 3.25/0.99  
% 3.25/0.99  sup_num_of_clauses:                     235
% 3.25/0.99  sup_num_in_active:                      91
% 3.25/0.99  sup_num_in_passive:                     144
% 3.25/0.99  sup_num_of_loops:                       92
% 3.25/0.99  sup_fw_superposition:                   192
% 3.25/0.99  sup_bw_superposition:                   69
% 3.25/0.99  sup_immediate_simplified:               36
% 3.25/0.99  sup_given_eliminated:                   0
% 3.25/0.99  comparisons_done:                       0
% 3.25/0.99  comparisons_avoided:                    0
% 3.25/0.99  
% 3.25/0.99  ------ Simplifications
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  sim_fw_subset_subsumed:                 0
% 3.25/0.99  sim_bw_subset_subsumed:                 1
% 3.25/0.99  sim_fw_subsumed:                        0
% 3.25/0.99  sim_bw_subsumed:                        0
% 3.25/0.99  sim_fw_subsumption_res:                 0
% 3.25/0.99  sim_bw_subsumption_res:                 0
% 3.25/0.99  sim_tautology_del:                      0
% 3.25/0.99  sim_eq_tautology_del:                   17
% 3.25/0.99  sim_eq_res_simp:                        0
% 3.25/0.99  sim_fw_demodulated:                     0
% 3.25/0.99  sim_bw_demodulated:                     2
% 3.25/0.99  sim_light_normalised:                   37
% 3.25/0.99  sim_joinable_taut:                      0
% 3.25/0.99  sim_joinable_simp:                      0
% 3.25/0.99  sim_ac_normalised:                      0
% 3.25/0.99  sim_smt_subsumption:                    0
% 3.25/0.99  
%------------------------------------------------------------------------------
