%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:03 EST 2020

% Result     : CounterSatisfiable 0.82s
% Output     : Saturation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 722 expanded)
%              Number of clauses        :   56 ( 146 expanded)
%              Number of leaves         :   21 ( 223 expanded)
%              Depth                    :   23
%              Number of atoms          :  372 (6424 expanded)
%              Number of equality atoms :  122 (1974 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( v6_yellow_0(X1,X0)
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
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( v4_yellow_0(X1,X0)
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
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ~ v2_struct_0(X1)
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
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ~ v2_struct_0(X1)
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
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ~ v2_struct_0(X1)
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
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0) )
       => ! [X1] :
            ( ~ v2_struct_0(X1)
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
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
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
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
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
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,X4,sK6) != k13_lattice3(X1,X2,X3)
        & sK6 = X3
        & X2 = X4
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( k13_lattice3(X0,sK5,X5) != k13_lattice3(X1,X2,X3)
            & X3 = X5
            & sK5 = X2
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                ( k13_lattice3(X1,X2,sK4) != k13_lattice3(X0,X4,X5)
                & sK4 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                    ( k13_lattice3(X1,sK3,X3) != k13_lattice3(X0,X4,X5)
                    & X3 = X5
                    & sK3 = X4
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k13_lattice3(sK2,X2,X3) != k13_lattice3(X0,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v1_lattice3(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k13_lattice3(sK1,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(sK1)) )
                      & m1_subset_1(X4,u1_struct_0(sK1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK1))
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & ~ v2_struct_0(sK2)
    & l1_orders_2(sK1)
    & v1_lattice3(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f26,f36,f35,f34,f33,f32,f31])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X0_47)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_267,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_264,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_261,plain,
    ( k2_tarski(X0_46,X1_46) = k2_tarski(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_172,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_173,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_181,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_173])).

cnf(c_182,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_17,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_32,plain,
    ( ~ l1_orders_2(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_35,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_17,c_16,c_26,c_32,c_35])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_184])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),X0_46,X1_46) = k2_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_143,plain,
    ( ~ v1_lattice3(X0)
    | v1_lattice3(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_142,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_141,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_138,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_137,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_134,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_254,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_255,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_256,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_257,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_316,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_319,plain,
    ( k7_domain_1(u1_struct_0(sK1),X0_46,X1_46) = k2_tarski(X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_515,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK5,X0_46) = k2_tarski(sK5,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_319])).

cnf(c_748,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK5,sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_316,c_515])).

cnf(c_315,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_747,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK5,sK6) = k2_tarski(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_315,c_515])).

cnf(c_514,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK6,X0_46) = k2_tarski(sK6,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_319])).

cnf(c_577,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK6,sK5) = k2_tarski(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_316,c_514])).

cnf(c_576,plain,
    ( k7_domain_1(u1_struct_0(sK1),sK6,sK6) = k2_tarski(sK6,sK6) ),
    inference(superposition,[status(thm)],[c_315,c_514])).

cnf(c_8,negated_conjecture,
    ( k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_260,negated_conjecture,
    ( k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_10,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_258,negated_conjecture,
    ( sK3 = sK5 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_9,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_259,negated_conjecture,
    ( sK4 = sK6 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_336,plain,
    ( k13_lattice3(sK2,sK5,sK6) != k13_lattice3(sK1,sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_260,c_258,c_259])).

cnf(c_318,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_331,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_318,c_258])).

cnf(c_317,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_328,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_317,c_259])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.82/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/0.99  
% 0.82/0.99  ------  iProver source info
% 0.82/0.99  
% 0.82/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.82/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/0.99  git: non_committed_changes: false
% 0.82/0.99  git: last_make_outside_of_git: false
% 0.82/0.99  
% 0.82/0.99  ------ 
% 0.82/0.99  
% 0.82/0.99  ------ Input Options
% 0.82/0.99  
% 0.82/0.99  --out_options                           all
% 0.82/0.99  --tptp_safe_out                         true
% 0.82/0.99  --problem_path                          ""
% 0.82/0.99  --include_path                          ""
% 0.82/0.99  --clausifier                            res/vclausify_rel
% 0.82/0.99  --clausifier_options                    --mode clausify
% 0.82/0.99  --stdin                                 false
% 0.82/0.99  --stats_out                             all
% 0.82/0.99  
% 0.82/0.99  ------ General Options
% 0.82/0.99  
% 0.82/0.99  --fof                                   false
% 0.82/0.99  --time_out_real                         305.
% 0.82/0.99  --time_out_virtual                      -1.
% 0.82/0.99  --symbol_type_check                     false
% 0.82/0.99  --clausify_out                          false
% 0.82/0.99  --sig_cnt_out                           false
% 0.82/0.99  --trig_cnt_out                          false
% 0.82/0.99  --trig_cnt_out_tolerance                1.
% 0.82/0.99  --trig_cnt_out_sk_spl                   false
% 0.82/0.99  --abstr_cl_out                          false
% 0.82/0.99  
% 0.82/0.99  ------ Global Options
% 0.82/0.99  
% 0.82/0.99  --schedule                              default
% 0.82/0.99  --add_important_lit                     false
% 0.82/0.99  --prop_solver_per_cl                    1000
% 0.82/0.99  --min_unsat_core                        false
% 0.82/0.99  --soft_assumptions                      false
% 0.82/0.99  --soft_lemma_size                       3
% 0.82/0.99  --prop_impl_unit_size                   0
% 0.82/0.99  --prop_impl_unit                        []
% 0.82/0.99  --share_sel_clauses                     true
% 0.82/0.99  --reset_solvers                         false
% 0.82/0.99  --bc_imp_inh                            [conj_cone]
% 0.82/0.99  --conj_cone_tolerance                   3.
% 0.82/0.99  --extra_neg_conj                        none
% 0.82/0.99  --large_theory_mode                     true
% 0.82/0.99  --prolific_symb_bound                   200
% 0.82/0.99  --lt_threshold                          2000
% 0.82/0.99  --clause_weak_htbl                      true
% 0.82/0.99  --gc_record_bc_elim                     false
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing Options
% 0.82/0.99  
% 0.82/0.99  --preprocessing_flag                    true
% 0.82/0.99  --time_out_prep_mult                    0.1
% 0.82/0.99  --splitting_mode                        input
% 0.82/0.99  --splitting_grd                         true
% 0.82/0.99  --splitting_cvd                         false
% 0.82/0.99  --splitting_cvd_svl                     false
% 0.82/0.99  --splitting_nvd                         32
% 0.82/0.99  --sub_typing                            true
% 0.82/0.99  --prep_gs_sim                           true
% 0.82/0.99  --prep_unflatten                        true
% 0.82/0.99  --prep_res_sim                          true
% 0.82/0.99  --prep_upred                            true
% 0.82/0.99  --prep_sem_filter                       exhaustive
% 0.82/0.99  --prep_sem_filter_out                   false
% 0.82/0.99  --pred_elim                             true
% 0.82/0.99  --res_sim_input                         true
% 0.82/0.99  --eq_ax_congr_red                       true
% 0.82/0.99  --pure_diseq_elim                       true
% 0.82/0.99  --brand_transform                       false
% 0.82/0.99  --non_eq_to_eq                          false
% 0.82/0.99  --prep_def_merge                        true
% 0.82/0.99  --prep_def_merge_prop_impl              false
% 0.82/0.99  --prep_def_merge_mbd                    true
% 0.82/0.99  --prep_def_merge_tr_red                 false
% 0.82/0.99  --prep_def_merge_tr_cl                  false
% 0.82/0.99  --smt_preprocessing                     true
% 0.82/0.99  --smt_ac_axioms                         fast
% 0.82/0.99  --preprocessed_out                      false
% 0.82/0.99  --preprocessed_stats                    false
% 0.82/0.99  
% 0.82/0.99  ------ Abstraction refinement Options
% 0.82/0.99  
% 0.82/0.99  --abstr_ref                             []
% 0.82/0.99  --abstr_ref_prep                        false
% 0.82/0.99  --abstr_ref_until_sat                   false
% 0.82/0.99  --abstr_ref_sig_restrict                funpre
% 0.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.99  --abstr_ref_under                       []
% 0.82/0.99  
% 0.82/0.99  ------ SAT Options
% 0.82/0.99  
% 0.82/0.99  --sat_mode                              false
% 0.82/0.99  --sat_fm_restart_options                ""
% 0.82/0.99  --sat_gr_def                            false
% 0.82/0.99  --sat_epr_types                         true
% 0.82/0.99  --sat_non_cyclic_types                  false
% 0.82/0.99  --sat_finite_models                     false
% 0.82/0.99  --sat_fm_lemmas                         false
% 0.82/0.99  --sat_fm_prep                           false
% 0.82/0.99  --sat_fm_uc_incr                        true
% 0.82/0.99  --sat_out_model                         small
% 0.82/0.99  --sat_out_clauses                       false
% 0.82/0.99  
% 0.82/0.99  ------ QBF Options
% 0.82/0.99  
% 0.82/0.99  --qbf_mode                              false
% 0.82/0.99  --qbf_elim_univ                         false
% 0.82/0.99  --qbf_dom_inst                          none
% 0.82/0.99  --qbf_dom_pre_inst                      false
% 0.82/0.99  --qbf_sk_in                             false
% 0.82/0.99  --qbf_pred_elim                         true
% 0.82/0.99  --qbf_split                             512
% 0.82/0.99  
% 0.82/0.99  ------ BMC1 Options
% 0.82/0.99  
% 0.82/0.99  --bmc1_incremental                      false
% 0.82/0.99  --bmc1_axioms                           reachable_all
% 0.82/0.99  --bmc1_min_bound                        0
% 0.82/0.99  --bmc1_max_bound                        -1
% 0.82/0.99  --bmc1_max_bound_default                -1
% 0.82/0.99  --bmc1_symbol_reachability              true
% 0.82/0.99  --bmc1_property_lemmas                  false
% 0.82/0.99  --bmc1_k_induction                      false
% 0.82/0.99  --bmc1_non_equiv_states                 false
% 0.82/0.99  --bmc1_deadlock                         false
% 0.82/0.99  --bmc1_ucm                              false
% 0.82/0.99  --bmc1_add_unsat_core                   none
% 0.82/0.99  --bmc1_unsat_core_children              false
% 0.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.99  --bmc1_out_stat                         full
% 0.82/0.99  --bmc1_ground_init                      false
% 0.82/0.99  --bmc1_pre_inst_next_state              false
% 0.82/0.99  --bmc1_pre_inst_state                   false
% 0.82/0.99  --bmc1_pre_inst_reach_state             false
% 0.82/0.99  --bmc1_out_unsat_core                   false
% 0.82/0.99  --bmc1_aig_witness_out                  false
% 0.82/0.99  --bmc1_verbose                          false
% 0.82/0.99  --bmc1_dump_clauses_tptp                false
% 0.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.99  --bmc1_dump_file                        -
% 0.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.99  --bmc1_ucm_extend_mode                  1
% 0.82/0.99  --bmc1_ucm_init_mode                    2
% 0.82/0.99  --bmc1_ucm_cone_mode                    none
% 0.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.99  --bmc1_ucm_relax_model                  4
% 0.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.99  --bmc1_ucm_layered_model                none
% 0.82/0.99  --bmc1_ucm_max_lemma_size               10
% 0.82/0.99  
% 0.82/0.99  ------ AIG Options
% 0.82/0.99  
% 0.82/0.99  --aig_mode                              false
% 0.82/0.99  
% 0.82/0.99  ------ Instantiation Options
% 0.82/0.99  
% 0.82/0.99  --instantiation_flag                    true
% 0.82/0.99  --inst_sos_flag                         false
% 0.82/0.99  --inst_sos_phase                        true
% 0.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel_side                     num_symb
% 0.82/0.99  --inst_solver_per_active                1400
% 0.82/0.99  --inst_solver_calls_frac                1.
% 0.82/0.99  --inst_passive_queue_type               priority_queues
% 0.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.99  --inst_passive_queues_freq              [25;2]
% 0.82/0.99  --inst_dismatching                      true
% 0.82/0.99  --inst_eager_unprocessed_to_passive     true
% 0.82/0.99  --inst_prop_sim_given                   true
% 0.82/0.99  --inst_prop_sim_new                     false
% 0.82/0.99  --inst_subs_new                         false
% 0.82/0.99  --inst_eq_res_simp                      false
% 0.82/0.99  --inst_subs_given                       false
% 0.82/0.99  --inst_orphan_elimination               true
% 0.82/0.99  --inst_learning_loop_flag               true
% 0.82/0.99  --inst_learning_start                   3000
% 0.82/0.99  --inst_learning_factor                  2
% 0.82/0.99  --inst_start_prop_sim_after_learn       3
% 0.82/0.99  --inst_sel_renew                        solver
% 0.82/0.99  --inst_lit_activity_flag                true
% 0.82/0.99  --inst_restr_to_given                   false
% 0.82/0.99  --inst_activity_threshold               500
% 0.82/0.99  --inst_out_proof                        true
% 0.82/0.99  
% 0.82/0.99  ------ Resolution Options
% 0.82/0.99  
% 0.82/0.99  --resolution_flag                       true
% 0.82/0.99  --res_lit_sel                           adaptive
% 0.82/0.99  --res_lit_sel_side                      none
% 0.82/0.99  --res_ordering                          kbo
% 0.82/0.99  --res_to_prop_solver                    active
% 0.82/0.99  --res_prop_simpl_new                    false
% 0.82/0.99  --res_prop_simpl_given                  true
% 0.82/0.99  --res_passive_queue_type                priority_queues
% 0.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.99  --res_passive_queues_freq               [15;5]
% 0.82/0.99  --res_forward_subs                      full
% 0.82/0.99  --res_backward_subs                     full
% 0.82/0.99  --res_forward_subs_resolution           true
% 0.82/0.99  --res_backward_subs_resolution          true
% 0.82/0.99  --res_orphan_elimination                true
% 0.82/0.99  --res_time_limit                        2.
% 0.82/0.99  --res_out_proof                         true
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Options
% 0.82/0.99  
% 0.82/0.99  --superposition_flag                    true
% 0.82/0.99  --sup_passive_queue_type                priority_queues
% 0.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.99  --demod_completeness_check              fast
% 0.82/0.99  --demod_use_ground                      true
% 0.82/0.99  --sup_to_prop_solver                    passive
% 0.82/0.99  --sup_prop_simpl_new                    true
% 0.82/0.99  --sup_prop_simpl_given                  true
% 0.82/0.99  --sup_fun_splitting                     false
% 0.82/0.99  --sup_smt_interval                      50000
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Simplification Setup
% 0.82/0.99  
% 0.82/0.99  --sup_indices_passive                   []
% 0.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_full_bw                           [BwDemod]
% 0.82/0.99  --sup_immed_triv                        [TrivRules]
% 0.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_immed_bw_main                     []
% 0.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  
% 0.82/0.99  ------ Combination Options
% 0.82/0.99  
% 0.82/0.99  --comb_res_mult                         3
% 0.82/0.99  --comb_sup_mult                         2
% 0.82/0.99  --comb_inst_mult                        10
% 0.82/0.99  
% 0.82/0.99  ------ Debug Options
% 0.82/0.99  
% 0.82/0.99  --dbg_backtrace                         false
% 0.82/0.99  --dbg_dump_prop_clauses                 false
% 0.82/0.99  --dbg_dump_prop_clauses_file            -
% 0.82/0.99  --dbg_out_stat                          false
% 0.82/0.99  ------ Parsing...
% 0.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/0.99  ------ Proving...
% 0.82/0.99  ------ Problem Properties 
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  clauses                                 9
% 0.82/0.99  conjectures                             7
% 0.82/0.99  EPR                                     2
% 0.82/0.99  Horn                                    9
% 0.82/0.99  unary                                   8
% 0.82/0.99  binary                                  0
% 0.82/0.99  lits                                    11
% 0.82/0.99  lits eq                                 5
% 0.82/0.99  fd_pure                                 0
% 0.82/0.99  fd_pseudo                               0
% 0.82/0.99  fd_cond                                 0
% 0.82/0.99  fd_pseudo_cond                          0
% 0.82/0.99  AC symbols                              0
% 0.82/0.99  
% 0.82/0.99  ------ Schedule dynamic 5 is on 
% 0.82/0.99  
% 0.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  ------ 
% 0.82/0.99  Current options:
% 0.82/0.99  ------ 
% 0.82/0.99  
% 0.82/0.99  ------ Input Options
% 0.82/0.99  
% 0.82/0.99  --out_options                           all
% 0.82/0.99  --tptp_safe_out                         true
% 0.82/0.99  --problem_path                          ""
% 0.82/0.99  --include_path                          ""
% 0.82/0.99  --clausifier                            res/vclausify_rel
% 0.82/0.99  --clausifier_options                    --mode clausify
% 0.82/0.99  --stdin                                 false
% 0.82/0.99  --stats_out                             all
% 0.82/0.99  
% 0.82/0.99  ------ General Options
% 0.82/0.99  
% 0.82/0.99  --fof                                   false
% 0.82/0.99  --time_out_real                         305.
% 0.82/0.99  --time_out_virtual                      -1.
% 0.82/0.99  --symbol_type_check                     false
% 0.82/0.99  --clausify_out                          false
% 0.82/0.99  --sig_cnt_out                           false
% 0.82/0.99  --trig_cnt_out                          false
% 0.82/0.99  --trig_cnt_out_tolerance                1.
% 0.82/0.99  --trig_cnt_out_sk_spl                   false
% 0.82/0.99  --abstr_cl_out                          false
% 0.82/0.99  
% 0.82/0.99  ------ Global Options
% 0.82/0.99  
% 0.82/0.99  --schedule                              default
% 0.82/0.99  --add_important_lit                     false
% 0.82/0.99  --prop_solver_per_cl                    1000
% 0.82/0.99  --min_unsat_core                        false
% 0.82/0.99  --soft_assumptions                      false
% 0.82/0.99  --soft_lemma_size                       3
% 0.82/0.99  --prop_impl_unit_size                   0
% 0.82/0.99  --prop_impl_unit                        []
% 0.82/0.99  --share_sel_clauses                     true
% 0.82/0.99  --reset_solvers                         false
% 0.82/0.99  --bc_imp_inh                            [conj_cone]
% 0.82/0.99  --conj_cone_tolerance                   3.
% 0.82/0.99  --extra_neg_conj                        none
% 0.82/0.99  --large_theory_mode                     true
% 0.82/0.99  --prolific_symb_bound                   200
% 0.82/0.99  --lt_threshold                          2000
% 0.82/0.99  --clause_weak_htbl                      true
% 0.82/0.99  --gc_record_bc_elim                     false
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing Options
% 0.82/0.99  
% 0.82/0.99  --preprocessing_flag                    true
% 0.82/0.99  --time_out_prep_mult                    0.1
% 0.82/0.99  --splitting_mode                        input
% 0.82/0.99  --splitting_grd                         true
% 0.82/0.99  --splitting_cvd                         false
% 0.82/0.99  --splitting_cvd_svl                     false
% 0.82/0.99  --splitting_nvd                         32
% 0.82/0.99  --sub_typing                            true
% 0.82/0.99  --prep_gs_sim                           true
% 0.82/0.99  --prep_unflatten                        true
% 0.82/0.99  --prep_res_sim                          true
% 0.82/0.99  --prep_upred                            true
% 0.82/0.99  --prep_sem_filter                       exhaustive
% 0.82/0.99  --prep_sem_filter_out                   false
% 0.82/0.99  --pred_elim                             true
% 0.82/0.99  --res_sim_input                         true
% 0.82/0.99  --eq_ax_congr_red                       true
% 0.82/0.99  --pure_diseq_elim                       true
% 0.82/0.99  --brand_transform                       false
% 0.82/0.99  --non_eq_to_eq                          false
% 0.82/0.99  --prep_def_merge                        true
% 0.82/0.99  --prep_def_merge_prop_impl              false
% 0.82/0.99  --prep_def_merge_mbd                    true
% 0.82/0.99  --prep_def_merge_tr_red                 false
% 0.82/0.99  --prep_def_merge_tr_cl                  false
% 0.82/0.99  --smt_preprocessing                     true
% 0.82/0.99  --smt_ac_axioms                         fast
% 0.82/0.99  --preprocessed_out                      false
% 0.82/0.99  --preprocessed_stats                    false
% 0.82/0.99  
% 0.82/0.99  ------ Abstraction refinement Options
% 0.82/0.99  
% 0.82/0.99  --abstr_ref                             []
% 0.82/0.99  --abstr_ref_prep                        false
% 0.82/0.99  --abstr_ref_until_sat                   false
% 0.82/0.99  --abstr_ref_sig_restrict                funpre
% 0.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.99  --abstr_ref_under                       []
% 0.82/0.99  
% 0.82/0.99  ------ SAT Options
% 0.82/0.99  
% 0.82/0.99  --sat_mode                              false
% 0.82/0.99  --sat_fm_restart_options                ""
% 0.82/0.99  --sat_gr_def                            false
% 0.82/0.99  --sat_epr_types                         true
% 0.82/0.99  --sat_non_cyclic_types                  false
% 0.82/0.99  --sat_finite_models                     false
% 0.82/0.99  --sat_fm_lemmas                         false
% 0.82/0.99  --sat_fm_prep                           false
% 0.82/0.99  --sat_fm_uc_incr                        true
% 0.82/0.99  --sat_out_model                         small
% 0.82/0.99  --sat_out_clauses                       false
% 0.82/0.99  
% 0.82/0.99  ------ QBF Options
% 0.82/0.99  
% 0.82/0.99  --qbf_mode                              false
% 0.82/0.99  --qbf_elim_univ                         false
% 0.82/0.99  --qbf_dom_inst                          none
% 0.82/0.99  --qbf_dom_pre_inst                      false
% 0.82/0.99  --qbf_sk_in                             false
% 0.82/0.99  --qbf_pred_elim                         true
% 0.82/0.99  --qbf_split                             512
% 0.82/0.99  
% 0.82/0.99  ------ BMC1 Options
% 0.82/0.99  
% 0.82/0.99  --bmc1_incremental                      false
% 0.82/0.99  --bmc1_axioms                           reachable_all
% 0.82/0.99  --bmc1_min_bound                        0
% 0.82/0.99  --bmc1_max_bound                        -1
% 0.82/0.99  --bmc1_max_bound_default                -1
% 0.82/0.99  --bmc1_symbol_reachability              true
% 0.82/0.99  --bmc1_property_lemmas                  false
% 0.82/0.99  --bmc1_k_induction                      false
% 0.82/0.99  --bmc1_non_equiv_states                 false
% 0.82/0.99  --bmc1_deadlock                         false
% 0.82/0.99  --bmc1_ucm                              false
% 0.82/0.99  --bmc1_add_unsat_core                   none
% 0.82/0.99  --bmc1_unsat_core_children              false
% 0.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.99  --bmc1_out_stat                         full
% 0.82/0.99  --bmc1_ground_init                      false
% 0.82/0.99  --bmc1_pre_inst_next_state              false
% 0.82/0.99  --bmc1_pre_inst_state                   false
% 0.82/0.99  --bmc1_pre_inst_reach_state             false
% 0.82/0.99  --bmc1_out_unsat_core                   false
% 0.82/0.99  --bmc1_aig_witness_out                  false
% 0.82/0.99  --bmc1_verbose                          false
% 0.82/0.99  --bmc1_dump_clauses_tptp                false
% 0.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.99  --bmc1_dump_file                        -
% 0.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.99  --bmc1_ucm_extend_mode                  1
% 0.82/0.99  --bmc1_ucm_init_mode                    2
% 0.82/0.99  --bmc1_ucm_cone_mode                    none
% 0.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.99  --bmc1_ucm_relax_model                  4
% 0.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.99  --bmc1_ucm_layered_model                none
% 0.82/0.99  --bmc1_ucm_max_lemma_size               10
% 0.82/0.99  
% 0.82/0.99  ------ AIG Options
% 0.82/0.99  
% 0.82/0.99  --aig_mode                              false
% 0.82/0.99  
% 0.82/0.99  ------ Instantiation Options
% 0.82/0.99  
% 0.82/0.99  --instantiation_flag                    true
% 0.82/0.99  --inst_sos_flag                         false
% 0.82/0.99  --inst_sos_phase                        true
% 0.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel_side                     none
% 0.82/0.99  --inst_solver_per_active                1400
% 0.82/0.99  --inst_solver_calls_frac                1.
% 0.82/0.99  --inst_passive_queue_type               priority_queues
% 0.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.99  --inst_passive_queues_freq              [25;2]
% 0.82/0.99  --inst_dismatching                      true
% 0.82/0.99  --inst_eager_unprocessed_to_passive     true
% 0.82/0.99  --inst_prop_sim_given                   true
% 0.82/0.99  --inst_prop_sim_new                     false
% 0.82/0.99  --inst_subs_new                         false
% 0.82/0.99  --inst_eq_res_simp                      false
% 0.82/0.99  --inst_subs_given                       false
% 0.82/0.99  --inst_orphan_elimination               true
% 0.82/0.99  --inst_learning_loop_flag               true
% 0.82/0.99  --inst_learning_start                   3000
% 0.82/0.99  --inst_learning_factor                  2
% 0.82/0.99  --inst_start_prop_sim_after_learn       3
% 0.82/0.99  --inst_sel_renew                        solver
% 0.82/0.99  --inst_lit_activity_flag                true
% 0.82/0.99  --inst_restr_to_given                   false
% 0.82/0.99  --inst_activity_threshold               500
% 0.82/0.99  --inst_out_proof                        true
% 0.82/0.99  
% 0.82/0.99  ------ Resolution Options
% 0.82/0.99  
% 0.82/0.99  --resolution_flag                       false
% 0.82/0.99  --res_lit_sel                           adaptive
% 0.82/0.99  --res_lit_sel_side                      none
% 0.82/0.99  --res_ordering                          kbo
% 0.82/0.99  --res_to_prop_solver                    active
% 0.82/0.99  --res_prop_simpl_new                    false
% 0.82/0.99  --res_prop_simpl_given                  true
% 0.82/0.99  --res_passive_queue_type                priority_queues
% 0.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.99  --res_passive_queues_freq               [15;5]
% 0.82/0.99  --res_forward_subs                      full
% 0.82/0.99  --res_backward_subs                     full
% 0.82/0.99  --res_forward_subs_resolution           true
% 0.82/0.99  --res_backward_subs_resolution          true
% 0.82/0.99  --res_orphan_elimination                true
% 0.82/0.99  --res_time_limit                        2.
% 0.82/0.99  --res_out_proof                         true
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Options
% 0.82/0.99  
% 0.82/0.99  --superposition_flag                    true
% 0.82/0.99  --sup_passive_queue_type                priority_queues
% 0.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.99  --demod_completeness_check              fast
% 0.82/0.99  --demod_use_ground                      true
% 0.82/0.99  --sup_to_prop_solver                    passive
% 0.82/0.99  --sup_prop_simpl_new                    true
% 0.82/0.99  --sup_prop_simpl_given                  true
% 0.82/0.99  --sup_fun_splitting                     false
% 0.82/0.99  --sup_smt_interval                      50000
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Simplification Setup
% 0.82/0.99  
% 0.82/0.99  --sup_indices_passive                   []
% 0.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_full_bw                           [BwDemod]
% 0.82/0.99  --sup_immed_triv                        [TrivRules]
% 0.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_immed_bw_main                     []
% 0.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  
% 0.82/0.99  ------ Combination Options
% 0.82/0.99  
% 0.82/0.99  --comb_res_mult                         3
% 0.82/0.99  --comb_sup_mult                         2
% 0.82/0.99  --comb_inst_mult                        10
% 0.82/0.99  
% 0.82/0.99  ------ Debug Options
% 0.82/0.99  
% 0.82/0.99  --dbg_backtrace                         false
% 0.82/0.99  --dbg_dump_prop_clauses                 false
% 0.82/0.99  --dbg_dump_prop_clauses_file            -
% 0.82/0.99  --dbg_out_stat                          false
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  ------ Proving...
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  % SZS output start Saturation for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  fof(f2,axiom,(
% 0.82/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f40,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f2])).
% 0.82/0.99  
% 0.82/0.99  fof(f6,axiom,(
% 0.82/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f21,plain,(
% 0.82/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.82/0.99    inference(ennf_transformation,[],[f6])).
% 0.82/0.99  
% 0.82/0.99  fof(f22,plain,(
% 0.82/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.82/0.99    inference(flattening,[],[f21])).
% 0.82/0.99  
% 0.82/0.99  fof(f44,plain,(
% 0.82/0.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f22])).
% 0.82/0.99  
% 0.82/0.99  fof(f4,axiom,(
% 0.82/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f18,plain,(
% 0.82/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.82/0.99    inference(ennf_transformation,[],[f4])).
% 0.82/0.99  
% 0.82/0.99  fof(f19,plain,(
% 0.82/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.82/0.99    inference(flattening,[],[f18])).
% 0.82/0.99  
% 0.82/0.99  fof(f42,plain,(
% 0.82/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f19])).
% 0.82/0.99  
% 0.82/0.99  fof(f5,axiom,(
% 0.82/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f20,plain,(
% 0.82/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.82/0.99    inference(ennf_transformation,[],[f5])).
% 0.82/0.99  
% 0.82/0.99  fof(f43,plain,(
% 0.82/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f20])).
% 0.82/0.99  
% 0.82/0.99  fof(f8,conjecture,(
% 0.82/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f9,negated_conjecture,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(negated_conjecture,[],[f8])).
% 0.82/0.99  
% 0.82/0.99  fof(f10,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f9])).
% 0.82/0.99  
% 0.82/0.99  fof(f11,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f10])).
% 0.82/0.99  
% 0.82/0.99  fof(f12,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f11])).
% 0.82/0.99  
% 0.82/0.99  fof(f13,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f12])).
% 0.82/0.99  
% 0.82/0.99  fof(f14,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f13])).
% 0.82/0.99  
% 0.82/0.99  fof(f15,plain,(
% 0.82/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.82/0.99    inference(pure_predicate_removal,[],[f14])).
% 0.82/0.99  
% 0.82/0.99  fof(f25,plain,(
% 0.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & (X3 = X5 & X2 = X4)) & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & (l1_orders_2(X0) & v1_lattice3(X0)))),
% 0.82/0.99    inference(ennf_transformation,[],[f15])).
% 0.82/0.99  
% 0.82/0.99  fof(f26,plain,(
% 0.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & v1_lattice3(X0))),
% 0.82/0.99    inference(flattening,[],[f25])).
% 0.82/0.99  
% 0.82/0.99  fof(f36,plain,(
% 0.82/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) => (k13_lattice3(X0,X4,sK6) != k13_lattice3(X1,X2,X3) & sK6 = X3 & X2 = X4 & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f35,plain,(
% 0.82/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) => (? [X5] : (k13_lattice3(X0,sK5,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & sK5 = X2 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f34,plain,(
% 0.82/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (? [X5] : (k13_lattice3(X1,X2,sK4) != k13_lattice3(X0,X4,X5) & sK4 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f33,plain,(
% 0.82/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X1,sK3,X3) != k13_lattice3(X0,X4,X5) & X3 = X5 & sK3 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f32,plain,(
% 0.82/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(sK2,X2,X3) != k13_lattice3(X0,X4,X5) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & ~v2_struct_0(sK2))) )),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f31,plain,(
% 0.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & v1_lattice3(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(sK1,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(sK1) & v1_lattice3(sK1))),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f37,plain,(
% 0.82/0.99    (((((k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK1))) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & ~v2_struct_0(sK2)) & l1_orders_2(sK1) & v1_lattice3(sK1)),
% 0.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f26,f36,f35,f34,f33,f32,f31])).
% 0.82/0.99  
% 0.82/0.99  fof(f47,plain,(
% 0.82/0.99    l1_orders_2(sK1)),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f46,plain,(
% 0.82/0.99    v1_lattice3(sK1)),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f7,axiom,(
% 0.82/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f23,plain,(
% 0.82/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.82/0.99    inference(ennf_transformation,[],[f7])).
% 0.82/0.99  
% 0.82/0.99  fof(f24,plain,(
% 0.82/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.82/0.99    inference(flattening,[],[f23])).
% 0.82/0.99  
% 0.82/0.99  fof(f45,plain,(
% 0.82/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f24])).
% 0.82/0.99  
% 0.82/0.99  fof(f49,plain,(
% 0.82/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f50,plain,(
% 0.82/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f51,plain,(
% 0.82/0.99    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f52,plain,(
% 0.82/0.99    m1_subset_1(sK6,u1_struct_0(sK1))),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f55,plain,(
% 0.82/0.99    k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4)),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f53,plain,(
% 0.82/0.99    sK3 = sK5),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  fof(f54,plain,(
% 0.82/0.99    sK4 = sK6),
% 0.82/0.99    inference(cnf_transformation,[],[f37])).
% 0.82/0.99  
% 0.82/0.99  cnf(c_269,plain,
% 0.82/0.99      ( ~ m1_subset_1(X0_46,X0_47)
% 0.82/0.99      | m1_subset_1(X1_46,X0_47)
% 0.82/0.99      | X1_46 != X0_46 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_267,plain,
% 0.82/0.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_264,plain,( X0_49 = X0_49 ),theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_2,plain,
% 0.82/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_261,plain,
% 0.82/0.99      ( k2_tarski(X0_46,X1_46) = k2_tarski(X1_46,X0_46) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_6,plain,
% 0.82/0.99      ( ~ m1_subset_1(X0,X1)
% 0.82/0.99      | ~ m1_subset_1(X2,X1)
% 0.82/0.99      | v1_xboole_0(X1)
% 0.82/0.99      | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f44]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_4,plain,
% 0.82/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f42]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_5,plain,
% 0.82/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f43]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_16,negated_conjecture,
% 0.82/0.99      ( l1_orders_2(sK1) ),
% 0.82/0.99      inference(cnf_transformation,[],[f47]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_172,plain,
% 0.82/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 0.82/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_173,plain,
% 0.82/0.99      ( l1_struct_0(sK1) ),
% 0.82/0.99      inference(unflattening,[status(thm)],[c_172]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_181,plain,
% 0.82/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 0.82/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_173]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_182,plain,
% 0.82/0.99      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 0.82/0.99      inference(unflattening,[status(thm)],[c_181]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_17,negated_conjecture,
% 0.82/0.99      ( v1_lattice3(sK1) ),
% 0.82/0.99      inference(cnf_transformation,[],[f46]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_7,plain,
% 0.82/0.99      ( ~ v1_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f45]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_26,plain,
% 0.82/0.99      ( ~ v1_lattice3(sK1) | ~ l1_orders_2(sK1) | ~ v2_struct_0(sK1) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_32,plain,
% 0.82/0.99      ( ~ l1_orders_2(sK1) | l1_struct_0(sK1) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_35,plain,
% 0.82/0.99      ( v2_struct_0(sK1)
% 0.82/0.99      | ~ l1_struct_0(sK1)
% 0.82/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_184,plain,
% 0.82/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 0.82/0.99      inference(global_propositional_subsumption,
% 0.82/0.99                [status(thm)],
% 0.82/0.99                [c_182,c_17,c_16,c_26,c_32,c_35]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_197,plain,
% 0.82/0.99      ( ~ m1_subset_1(X0,X1)
% 0.82/0.99      | ~ m1_subset_1(X2,X1)
% 0.82/0.99      | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
% 0.82/0.99      | u1_struct_0(sK1) != X1 ),
% 0.82/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_184]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_198,plain,
% 0.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.82/0.99      | k7_domain_1(u1_struct_0(sK1),X0,X1) = k2_tarski(X0,X1) ),
% 0.82/0.99      inference(unflattening,[status(thm)],[c_197]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_253,plain,
% 0.82/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 0.82/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 0.82/0.99      | k7_domain_1(u1_struct_0(sK1),X0_46,X1_46) = k2_tarski(X0_46,X1_46) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_198]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_143,plain,
% 0.82/0.99      ( ~ v1_lattice3(X0) | v1_lattice3(X1) | X1 != X0 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_142,plain,
% 0.82/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_141,plain,
% 0.82/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_138,plain,
% 0.82/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_137,plain,
% 0.82/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_134,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_14,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f49]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_254,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_13,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f50]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_255,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_12,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f51]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_256,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_11,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f52]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_257,negated_conjecture,
% 0.82/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_316,plain,
% 0.82/0.99      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_319,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),X0_46,X1_46) = k2_tarski(X0_46,X1_46)
% 0.82/0.99      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 0.82/0.99      | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_515,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK5,X0_46) = k2_tarski(sK5,X0_46)
% 0.82/0.99      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_316,c_319]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_748,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK5,sK5) = k2_tarski(sK5,sK5) ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_316,c_515]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_315,plain,
% 0.82/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_747,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK5,sK6) = k2_tarski(sK5,sK6) ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_315,c_515]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_514,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK6,X0_46) = k2_tarski(sK6,X0_46)
% 0.82/0.99      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_315,c_319]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_577,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK6,sK5) = k2_tarski(sK6,sK5) ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_316,c_514]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_576,plain,
% 0.82/0.99      ( k7_domain_1(u1_struct_0(sK1),sK6,sK6) = k2_tarski(sK6,sK6) ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_315,c_514]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_8,negated_conjecture,
% 0.82/0.99      ( k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) ),
% 0.82/0.99      inference(cnf_transformation,[],[f55]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_260,negated_conjecture,
% 0.82/0.99      ( k13_lattice3(sK1,sK5,sK6) != k13_lattice3(sK2,sK3,sK4) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_10,negated_conjecture,
% 0.82/0.99      ( sK3 = sK5 ),
% 0.82/0.99      inference(cnf_transformation,[],[f53]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_258,negated_conjecture,
% 0.82/0.99      ( sK3 = sK5 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_9,negated_conjecture,
% 0.82/0.99      ( sK4 = sK6 ),
% 0.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_259,negated_conjecture,
% 0.82/0.99      ( sK4 = sK6 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_336,plain,
% 0.82/0.99      ( k13_lattice3(sK2,sK5,sK6) != k13_lattice3(sK1,sK5,sK6) ),
% 0.82/0.99      inference(light_normalisation,[status(thm)],[c_260,c_258,c_259]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_318,plain,
% 0.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_331,plain,
% 0.82/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 0.82/0.99      inference(light_normalisation,[status(thm)],[c_318,c_258]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_317,plain,
% 0.82/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_328,plain,
% 0.82/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 0.82/0.99      inference(light_normalisation,[status(thm)],[c_317,c_259]) ).
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  % SZS output end Saturation for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  ------                               Statistics
% 0.82/0.99  
% 0.82/0.99  ------ General
% 0.82/0.99  
% 0.82/0.99  abstr_ref_over_cycles:                  0
% 0.82/0.99  abstr_ref_under_cycles:                 0
% 0.82/0.99  gc_basic_clause_elim:                   0
% 0.82/0.99  forced_gc_time:                         0
% 0.82/0.99  parsing_time:                           0.008
% 0.82/0.99  unif_index_cands_time:                  0.
% 0.82/0.99  unif_index_add_time:                    0.
% 0.82/0.99  orderings_time:                         0.
% 0.82/0.99  out_proof_time:                         0.
% 0.82/0.99  total_time:                             0.062
% 0.82/0.99  num_of_symbols:                         51
% 0.82/0.99  num_of_terms:                           723
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing
% 0.82/0.99  
% 0.82/0.99  num_of_splits:                          0
% 0.82/0.99  num_of_split_atoms:                     0
% 0.82/0.99  num_of_reused_defs:                     0
% 0.82/0.99  num_eq_ax_congr_red:                    20
% 0.82/0.99  num_of_sem_filtered_clauses:            10
% 0.82/0.99  num_of_subtypes:                        5
% 0.82/0.99  monotx_restored_types:                  0
% 0.82/0.99  sat_num_of_epr_types:                   0
% 0.82/0.99  sat_num_of_non_cyclic_types:            0
% 0.82/0.99  sat_guarded_non_collapsed_types:        0
% 0.82/0.99  num_pure_diseq_elim:                    0
% 0.82/0.99  simp_replaced_by:                       0
% 0.82/0.99  res_preprocessed:                       53
% 0.82/0.99  prep_upred:                             0
% 0.82/0.99  prep_unflattend:                        6
% 0.82/0.99  smt_new_axioms:                         0
% 0.82/0.99  pred_elim_cands:                        1
% 0.82/0.99  pred_elim:                              6
% 0.82/0.99  pred_elim_cl:                           9
% 0.82/0.99  pred_elim_cycles:                       8
% 0.82/0.99  merged_defs:                            0
% 0.82/0.99  merged_defs_ncl:                        0
% 0.82/0.99  bin_hyper_res:                          0
% 0.82/0.99  prep_cycles:                            4
% 0.82/0.99  pred_elim_time:                         0.001
% 0.82/0.99  splitting_time:                         0.
% 0.82/0.99  sem_filter_time:                        0.
% 0.82/0.99  monotx_time:                            0.
% 0.82/0.99  subtype_inf_time:                       0.
% 0.82/0.99  
% 0.82/0.99  ------ Problem properties
% 0.82/0.99  
% 0.82/0.99  clauses:                                9
% 0.82/0.99  conjectures:                            7
% 0.82/0.99  epr:                                    2
% 0.82/0.99  horn:                                   9
% 0.82/0.99  ground:                                 7
% 0.82/0.99  unary:                                  8
% 0.82/0.99  binary:                                 0
% 0.82/0.99  lits:                                   11
% 0.82/0.99  lits_eq:                                5
% 0.82/0.99  fd_pure:                                0
% 0.82/0.99  fd_pseudo:                              0
% 0.82/0.99  fd_cond:                                0
% 0.82/0.99  fd_pseudo_cond:                         0
% 0.82/0.99  ac_symbols:                             0
% 0.82/0.99  
% 0.82/0.99  ------ Propositional Solver
% 0.82/0.99  
% 0.82/0.99  prop_solver_calls:                      29
% 0.82/0.99  prop_fast_solver_calls:                 199
% 0.82/0.99  smt_solver_calls:                       0
% 0.82/0.99  smt_fast_solver_calls:                  0
% 0.82/0.99  prop_num_of_clauses:                    238
% 0.82/0.99  prop_preprocess_simplified:             1116
% 0.82/0.99  prop_fo_subsumed:                       2
% 0.82/0.99  prop_solver_time:                       0.
% 0.82/0.99  smt_solver_time:                        0.
% 0.82/0.99  smt_fast_solver_time:                   0.
% 0.82/0.99  prop_fast_solver_time:                  0.
% 0.82/0.99  prop_unsat_core_time:                   0.
% 0.82/0.99  
% 0.82/0.99  ------ QBF
% 0.82/0.99  
% 0.82/0.99  qbf_q_res:                              0
% 0.82/0.99  qbf_num_tautologies:                    0
% 0.82/0.99  qbf_prep_cycles:                        0
% 0.82/0.99  
% 0.82/0.99  ------ BMC1
% 0.82/0.99  
% 0.82/0.99  bmc1_current_bound:                     -1
% 0.82/0.99  bmc1_last_solved_bound:                 -1
% 0.82/0.99  bmc1_unsat_core_size:                   -1
% 0.82/0.99  bmc1_unsat_core_parents_size:           -1
% 0.82/0.99  bmc1_merge_next_fun:                    0
% 0.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.82/0.99  
% 0.82/0.99  ------ Instantiation
% 0.82/0.99  
% 0.82/0.99  inst_num_of_clauses:                    99
% 0.82/0.99  inst_num_in_passive:                    6
% 0.82/0.99  inst_num_in_active:                     76
% 0.82/0.99  inst_num_in_unprocessed:                17
% 0.82/0.99  inst_num_of_loops:                      80
% 0.82/0.99  inst_num_of_learning_restarts:          0
% 0.82/0.99  inst_num_moves_active_passive:          0
% 0.82/0.99  inst_lit_activity:                      0
% 0.82/0.99  inst_lit_activity_moves:                0
% 0.82/0.99  inst_num_tautologies:                   0
% 0.82/0.99  inst_num_prop_implied:                  0
% 0.82/0.99  inst_num_existing_simplified:           0
% 0.82/0.99  inst_num_eq_res_simplified:             0
% 0.82/0.99  inst_num_child_elim:                    0
% 0.82/0.99  inst_num_of_dismatching_blockings:      38
% 0.82/0.99  inst_num_of_non_proper_insts:           175
% 0.82/0.99  inst_num_of_duplicates:                 0
% 0.82/0.99  inst_inst_num_from_inst_to_res:         0
% 0.82/0.99  inst_dismatching_checking_time:         0.
% 0.82/0.99  
% 0.82/0.99  ------ Resolution
% 0.82/0.99  
% 0.82/0.99  res_num_of_clauses:                     0
% 0.82/0.99  res_num_in_passive:                     0
% 0.82/0.99  res_num_in_active:                      0
% 0.82/0.99  res_num_of_loops:                       57
% 0.82/0.99  res_forward_subset_subsumed:            66
% 0.82/0.99  res_backward_subset_subsumed:           0
% 0.82/0.99  res_forward_subsumed:                   0
% 0.82/0.99  res_backward_subsumed:                  0
% 0.82/0.99  res_forward_subsumption_resolution:     0
% 0.82/0.99  res_backward_subsumption_resolution:    0
% 0.82/0.99  res_clause_to_clause_subsumption:       19
% 0.82/0.99  res_orphan_elimination:                 0
% 0.82/0.99  res_tautology_del:                      31
% 0.82/0.99  res_num_eq_res_simplified:              0
% 0.82/0.99  res_num_sel_changes:                    0
% 0.82/0.99  res_moves_from_active_to_pass:          0
% 0.82/0.99  
% 0.82/0.99  ------ Superposition
% 0.82/0.99  
% 0.82/0.99  sup_time_total:                         0.
% 0.82/0.99  sup_time_generating:                    0.
% 0.82/0.99  sup_time_sim_full:                      0.
% 0.82/0.99  sup_time_sim_immed:                     0.
% 0.82/0.99  
% 0.82/0.99  sup_num_of_clauses:                     15
% 0.82/0.99  sup_num_in_active:                      15
% 0.82/0.99  sup_num_in_passive:                     0
% 0.82/0.99  sup_num_of_loops:                       15
% 0.82/0.99  sup_fw_superposition:                   6
% 0.82/0.99  sup_bw_superposition:                   0
% 0.82/0.99  sup_immediate_simplified:               0
% 0.82/0.99  sup_given_eliminated:                   0
% 0.82/0.99  comparisons_done:                       0
% 0.82/0.99  comparisons_avoided:                    0
% 0.82/0.99  
% 0.82/0.99  ------ Simplifications
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  sim_fw_subset_subsumed:                 0
% 0.82/0.99  sim_bw_subset_subsumed:                 0
% 0.82/0.99  sim_fw_subsumed:                        0
% 0.82/0.99  sim_bw_subsumed:                        0
% 0.82/0.99  sim_fw_subsumption_res:                 0
% 0.82/0.99  sim_bw_subsumption_res:                 0
% 0.82/0.99  sim_tautology_del:                      0
% 0.82/0.99  sim_eq_tautology_del:                   0
% 0.82/0.99  sim_eq_res_simp:                        0
% 0.82/0.99  sim_fw_demodulated:                     0
% 0.82/0.99  sim_bw_demodulated:                     0
% 0.82/0.99  sim_light_normalised:                   3
% 0.82/0.99  sim_joinable_taut:                      0
% 0.82/0.99  sim_joinable_simp:                      0
% 0.82/0.99  sim_ac_normalised:                      0
% 0.82/0.99  sim_smt_subsumption:                    0
% 0.82/0.99  
%------------------------------------------------------------------------------
