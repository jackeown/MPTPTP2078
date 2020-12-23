%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1592+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:59 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  257 (2385 expanded)
%              Number of clauses        :  162 ( 519 expanded)
%              Number of leaves         :   29 (1001 expanded)
%              Depth                    :   23
%              Number of atoms          : 1154 (25868 expanded)
%              Number of equality atoms :  230 (7052 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X0))
                         => ( ( X3 = X5
                              & X2 = X4 )
                           => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,X4,sK9) != k13_lattice3(X1,X2,X3)
        & sK9 = X3
        & X2 = X4
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( k13_lattice3(X0,sK8,X5) != k13_lattice3(X1,X2,X3)
            & X3 = X5
            & sK8 = X2
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k13_lattice3(X1,X2,sK7) != k13_lattice3(X0,X4,X5)
                & sK7 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k13_lattice3(X1,sK6,X3) != k13_lattice3(X0,X4,X5)
                    & X3 = X5
                    & sK6 = X4
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v6_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k13_lattice3(sK5,X2,X3) != k13_lattice3(X0,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK5)) )
            & m1_subset_1(X2,u1_struct_0(sK5)) )
        & m1_yellow_0(sK5,X0)
        & v6_yellow_0(sK5,X0)
        & v4_yellow_0(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(sK4,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(sK4)) )
                      & m1_subset_1(X4,u1_struct_0(sK4)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK4)
          & v6_yellow_0(X1,sK4)
          & v4_yellow_0(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( k13_lattice3(sK4,sK8,sK9) != k13_lattice3(sK5,sK6,sK7)
    & sK7 = sK9
    & sK6 = sK8
    & m1_subset_1(sK9,u1_struct_0(sK4))
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & m1_yellow_0(sK5,sK4)
    & v6_yellow_0(sK5,sK4)
    & v4_yellow_0(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_orders_2(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f47,f63,f62,f61,f60,f59,f58])).

fof(f108,plain,(
    m1_subset_1(sK9,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                        & r2_hidden(X3,u1_struct_0(X1))
                        & r2_hidden(X2,u1_struct_0(X1)) )
                     => r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_yellow_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      & r2_hidden(X3,u1_struct_0(X1))
                      & r2_hidden(X2,u1_struct_0(X1))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      | ~ r2_hidden(X3,u1_struct_0(X1))
                      | ~ r2_hidden(X2,u1_struct_0(X1))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v6_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_yellow_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      & r2_hidden(X3,u1_struct_0(X1))
                      & r2_hidden(X2,u1_struct_0(X1))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
                      | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
                      | ~ r2_hidden(X5,u1_struct_0(X1))
                      | ~ r2_hidden(X4,u1_struct_0(X1))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v6_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
          & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
          & r2_hidden(X3,u1_struct_0(X1))
          & r2_hidden(X2,u1_struct_0(X1))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,sK1(X0,X1))),u1_struct_0(X1))
        & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),u1_struct_0(X1))
        & r2_hidden(X2,u1_struct_0(X1))
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
              & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
              & r2_hidden(X3,u1_struct_0(X1))
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK0(X0,X1),X3)),u1_struct_0(X1))
            & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK0(X0,X1),X3))
            & r2_hidden(X3,u1_struct_0(X1))
            & r2_hidden(sK0(X0,X1),u1_struct_0(X1))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_yellow_0(X1,X0)
              | ( ~ r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK0(X0,X1),sK1(X0,X1))),u1_struct_0(X1))
                & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK0(X0,X1),sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),u1_struct_0(X1))
                & r2_hidden(sK0(X0,X1),u1_struct_0(X1))
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
                      | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
                      | ~ r2_hidden(X5,u1_struct_0(X1))
                      | ~ r2_hidden(X4,u1_struct_0(X1))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v6_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f76,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
      | ~ r2_hidden(X5,u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v6_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    m1_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,(
    v6_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    sK6 = sK8 ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f110,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
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

fof(f38,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r1_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,k2_tarski(sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f56,f55])).

fof(f88,plain,(
    ! [X4,X0,X3] :
      ( r1_yellow_0(X0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f96,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    v4_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v4_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v4_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v5_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v5_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v3_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( ( v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v6_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & v1_lattice3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v1_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v6_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v1_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v6_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_lattice3(X1)
      | ~ v6_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    k13_lattice3(sK4,sK8,sK9) != k13_lattice3(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1094,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1420,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1093,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1421,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_19,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_424,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_21])).

cnf(c_4,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_43,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_746,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_43])).

cnf(c_747,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_42,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_117,plain,
    ( ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_749,plain,
    ( ~ v2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_747,c_43,c_42,c_117])).

cnf(c_842,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_424,c_749])).

cnf(c_843,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_80,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_84,plain,
    ( l1_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_845,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_43,c_42,c_80,c_84,c_117])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_845])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),X0_58,X1_58) = k2_tarski(X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_870])).

cnf(c_1432,plain,
    ( k7_domain_1(u1_struct_0(sK4),X0_58,X1_58) = k2_tarski(X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_2286,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK8,X0_58) = k2_tarski(sK8,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1432])).

cnf(c_2405,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK8,sK9) = k2_tarski(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1420,c_2286])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0))
    | ~ r2_hidden(X0,u1_struct_0(X3))
    | ~ r2_hidden(X2,u1_struct_0(X3))
    | r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)),u1_struct_0(X3))
    | ~ m1_yellow_0(X3,X1)
    | ~ v6_yellow_0(X3,X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( m1_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2))
    | ~ r2_hidden(X2,u1_struct_0(X3))
    | ~ r2_hidden(X0,u1_struct_0(X3))
    | r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)),u1_struct_0(X3))
    | ~ v6_yellow_0(X3,X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK5 != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,u1_struct_0(sK5))
    | r2_hidden(k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0)),u1_struct_0(sK5))
    | ~ v6_yellow_0(sK5,sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_39,negated_conjecture,
    ( v6_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_789,plain,
    ( r2_hidden(k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0)),u1_struct_0(sK5))
    | ~ r2_hidden(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_43,c_42,c_39,c_117])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0))
    | ~ r2_hidden(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,u1_struct_0(sK5))
    | r2_hidden(k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1,X0)),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_789])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1_58,X0_58))
    | ~ r2_hidden(X0_58,u1_struct_0(sK5))
    | ~ r2_hidden(X1_58,u1_struct_0(sK5))
    | r2_hidden(k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1_58,X0_58)),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_790])).

cnf(c_1428,plain,
    ( m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1_58,X0_58)) != iProver_top
    | r2_hidden(X1_58,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_58,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X1_58,X0_58)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_2515,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,k2_tarski(sK8,sK9)),u1_struct_0(sK5)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_1428])).

cnf(c_2576,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,k2_tarski(sK8,sK9)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,k2_tarski(sK8,sK9)),u1_struct_0(sK5)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2515,c_2405])).

cnf(c_58,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_59,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1091,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1423,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_33,negated_conjecture,
    ( sK6 = sK8 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1095,negated_conjecture,
    ( sK6 = sK8 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1448,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1423,c_1095])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1092,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1422,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_32,negated_conjecture,
    ( sK7 = sK9 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1096,negated_conjecture,
    ( sK7 = sK9 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1445,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1422,c_1096])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_831,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_424,c_41])).

cnf(c_832,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_20,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_761,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_762,plain,
    ( l1_orders_2(sK5)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_834,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_42,c_762])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_834])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_1080,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | r2_hidden(X0_58,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_900])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | r2_hidden(sK9,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1766,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_1768,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | r2_hidden(sK8,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1769,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1768])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_yellow_0(X1,k2_tarski(X2,X0))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_yellow_0(X1,k2_tarski(X0,X2))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_44])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X1,X0))
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_43,c_42])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_685])).

cnf(c_1575,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(X0_58,sK9)) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | r1_yellow_0(sK4,k2_tarski(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1928,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,k2_tarski(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1927])).

cnf(c_5102,plain,
    ( r2_hidden(k1_yellow_0(sK4,k2_tarski(sK8,sK9)),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_58,c_59,c_1448,c_1445,c_1766,c_1769,c_1928])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)) = k13_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k13_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_45])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k13_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_46,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k13_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_46,c_44,c_43,c_42])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK4))
    | k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k13_lattice3(sK4,X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_1426,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k13_lattice3(sK4,X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_1962,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,X0_58)) = k13_lattice3(sK4,sK8,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1426])).

cnf(c_2113,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) = k13_lattice3(sK4,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1420,c_1962])).

cnf(c_2488,plain,
    ( k1_yellow_0(sK4,k2_tarski(sK8,sK9)) = k13_lattice3(sK4,sK8,sK9) ),
    inference(demodulation,[status(thm)],[c_2405,c_2113])).

cnf(c_5106,plain,
    ( r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5102,c_2488])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | ~ r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_yellow_0(X1,X0) = k1_yellow_0(X2,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,negated_conjecture,
    ( v4_yellow_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | ~ r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_yellow_0(X1,X0) = k1_yellow_0(X2,X0)
    | sK5 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_yellow_0(sK4,X0)
    | ~ r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK5))
    | ~ m1_yellow_0(sK5,sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_45,c_43,c_42,c_41,c_38,c_117])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_yellow_0(sK4,X0)
    | ~ r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0) ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_1089,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_yellow_0(sK4,X0_58)
    | ~ r2_hidden(k1_yellow_0(sK4,X0_58),u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0_58) = k1_yellow_0(sK4,X0_58) ),
    inference(subtyping,[status(esa)],[c_590])).

cnf(c_1425,plain,
    ( k1_yellow_0(sK5,X0_58) = k1_yellow_0(sK4,X0_58)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_yellow_0(sK4,X0_58) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0_58),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_2174,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) = k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) != iProver_top
    | r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_1425])).

cnf(c_2179,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) = k13_lattice3(sK4,sK8,sK9)
    | m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) != iProver_top
    | r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2174,c_2113])).

cnf(c_1551,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1448])).

cnf(c_1554,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1445])).

cnf(c_1103,plain,
    ( ~ r1_yellow_0(X0_60,X0_58)
    | r1_yellow_0(X0_60,X1_58)
    | X1_58 != X0_58 ),
    theory(equality)).

cnf(c_1692,plain,
    ( r1_yellow_0(sK4,X0_58)
    | ~ r1_yellow_0(sK4,k2_tarski(X1_58,sK9))
    | X0_58 != k2_tarski(X1_58,sK9) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1810,plain,
    ( r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9))
    | ~ r1_yellow_0(sK4,k2_tarski(sK8,sK9))
    | k7_domain_1(u1_struct_0(sK4),sK8,sK9) != k2_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1812,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK8,sK9) != k2_tarski(sK8,sK9)
    | r1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) = iProver_top
    | r1_yellow_0(sK4,k2_tarski(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_1628,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),sK8,X0_58) = k2_tarski(sK8,X0_58) ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1811,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | k7_domain_1(u1_struct_0(sK4),sK8,sK9) = k2_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1100,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_2304,plain,
    ( X0_58 != X1_58
    | k7_domain_1(u1_struct_0(sK4),sK8,X2_58) != X1_58
    | k7_domain_1(u1_struct_0(sK4),sK8,X2_58) = X0_58 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_2703,plain,
    ( X0_58 != k2_tarski(sK8,X1_58)
    | k7_domain_1(u1_struct_0(sK4),sK8,X1_58) = X0_58
    | k7_domain_1(u1_struct_0(sK4),sK8,X1_58) != k2_tarski(sK8,X1_58) ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_2854,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK8,sK9) != k2_tarski(sK8,sK9)
    | k7_domain_1(u1_struct_0(sK4),sK8,sK9) = k7_domain_1(u1_struct_0(sK5),sK8,sK9)
    | k7_domain_1(u1_struct_0(sK4),sK8,sK9) != k2_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_834])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),X0_58,X1_58) = k2_tarski(X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_912])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),X0_58,sK9) = k2_tarski(X0_58,sK9) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_2855,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),sK8,sK9) = k2_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_1104,plain,
    ( ~ m1_subset_1(X0_58,X0_59)
    | m1_subset_1(X1_58,X0_59)
    | X1_58 != X0_58 ),
    theory(equality)).

cnf(c_1663,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK5),X1_58,X2_58),k1_zfmisc_1(u1_struct_0(sK5)))
    | X0_58 != k7_domain_1(u1_struct_0(sK5),X1_58,X2_58) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_3011,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | k7_domain_1(u1_struct_0(sK4),sK8,sK9) != k7_domain_1(u1_struct_0(sK5),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_3012,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK8,sK9) != k7_domain_1(u1_struct_0(sK5),sK8,sK9)
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK4),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_926,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_834])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),X0,X1),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK5))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),X0_58,X1_58),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_927])).

cnf(c_2150,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK5),X0_58,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_4049,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_4050,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK5),sK8,sK9),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4049])).

cnf(c_4864,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK4),sK8,sK9)) = k13_lattice3(sK4,sK8,sK9)
    | r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2179,c_35,c_58,c_34,c_59,c_1448,c_1551,c_1445,c_1554,c_1812,c_1811,c_1928,c_2854,c_2855,c_3012,c_4050])).

cnf(c_1435,plain,
    ( k7_domain_1(u1_struct_0(sK5),X0_58,X1_58) = k2_tarski(X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_3333,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK8,X0_58) = k2_tarski(sK8,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1435])).

cnf(c_3852,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK8,sK9) = k2_tarski(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1445,c_3333])).

cnf(c_764,plain,
    ( l1_orders_2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_42])).

cnf(c_8,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_527,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_40])).

cnf(c_528,plain,
    ( ~ m1_yellow_0(sK5,sK4)
    | v4_orders_2(sK5)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_530,plain,
    ( v4_orders_2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_45,c_42,c_38])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k13_lattice3(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_530])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | ~ l1_orders_2(sK5)
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_10,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ v5_orders_2(X1)
    | v5_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_516,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v5_orders_2(X1)
    | v5_orders_2(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_40])).

cnf(c_517,plain,
    ( ~ m1_yellow_0(sK5,sK4)
    | v5_orders_2(sK5)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_6,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ v3_orders_2(X1)
    | v3_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_538,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v3_orders_2(X1)
    | v3_orders_2(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_40])).

cnf(c_539,plain,
    ( ~ m1_yellow_0(sK5,sK4)
    | v3_orders_2(sK5)
    | ~ v3_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_2,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ v6_yellow_0(X0,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_lattice3(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_549,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v6_yellow_0(X0,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_lattice3(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X0)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_40])).

cnf(c_550,plain,
    ( ~ m1_yellow_0(sK5,sK4)
    | ~ v6_yellow_0(sK5,sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_lattice3(sK5)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5)
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_46,c_45,c_44,c_43,c_42,c_41,c_39,c_38,c_517,c_539,c_550])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5)
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_764,c_653])).

cnf(c_1085,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK5))
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0_58,X1_58)) = k13_lattice3(sK5,X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_1429,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0_58,X1_58)) = k13_lattice3(sK5,X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_2796,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK8,X0_58)) = k13_lattice3(sK5,sK8,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1429])).

cnf(c_3078,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK8,sK9)) = k13_lattice3(sK5,sK8,sK9) ),
    inference(superposition,[status(thm)],[c_1445,c_2796])).

cnf(c_3859,plain,
    ( k1_yellow_0(sK5,k2_tarski(sK8,sK9)) = k13_lattice3(sK5,sK8,sK9) ),
    inference(demodulation,[status(thm)],[c_3852,c_3078])).

cnf(c_4868,plain,
    ( k13_lattice3(sK5,sK8,sK9) = k13_lattice3(sK4,sK8,sK9)
    | r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4864,c_2405,c_3859])).

cnf(c_31,negated_conjecture,
    ( k13_lattice3(sK4,sK8,sK9) != k13_lattice3(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1097,negated_conjecture,
    ( k13_lattice3(sK4,sK8,sK9) != k13_lattice3(sK5,sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1451,plain,
    ( k13_lattice3(sK5,sK8,sK9) != k13_lattice3(sK4,sK8,sK9) ),
    inference(light_normalisation,[status(thm)],[c_1097,c_1095,c_1096])).

cnf(c_4871,plain,
    ( r2_hidden(k13_lattice3(sK4,sK8,sK9),u1_struct_0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4868,c_1451])).

cnf(c_5108,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5106,c_4871])).


%------------------------------------------------------------------------------
