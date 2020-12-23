%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:03 EST 2020

% Result     : CounterSatisfiable 0.76s
% Output     : Saturation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  110 (1230 expanded)
%              Number of clauses        :   65 ( 244 expanded)
%              Number of leaves         :   17 ( 368 expanded)
%              Depth                    :   25
%              Number of atoms          :  407 (10816 expanded)
%              Number of equality atoms :  132 (3250 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f10,plain,(
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
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,X4,sK5) != k13_lattice3(X1,X2,X3)
        & sK5 = X3
        & X2 = X4
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( k13_lattice3(X0,sK4,X5) != k13_lattice3(X1,X2,X3)
            & X3 = X5
            & sK4 = X2
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
                ( k13_lattice3(X1,X2,sK3) != k13_lattice3(X0,X4,X5)
                & sK3 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                    ( k13_lattice3(X1,sK2,X3) != k13_lattice3(X0,X4,X5)
                    & X3 = X5
                    & sK2 = X4
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                        ( k13_lattice3(sK1,X2,X3) != k13_lattice3(X0,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
                          ( k13_lattice3(sK0,X4,X5) != k13_lattice3(X1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3)
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v1_lattice3(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f32,f31,f30,f29,f28,f27])).

fof(f45,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_118,plain,
    ( ~ v1_lattice3(X0)
    | v1_lattice3(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_117,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_115,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_114,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_258,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_254,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_371,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_253,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_372,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_145,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_146,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_154,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_146])).

cnf(c_155,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_14,negated_conjecture,
    ( v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_29,plain,
    ( ~ l1_orders_2(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_35,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_157,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_155,c_14,c_13,c_23,c_29,c_35])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_157])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),X0_45,X1_45) = k2_tarski(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_168])).

cnf(c_375,plain,
    ( k7_domain_1(u1_struct_0(sK0),X0_45,X1_45) = k2_tarski(X0_45,X1_45)
    | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_549,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK4,X0_45) = k2_tarski(sK4,X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_372,c_375])).

cnf(c_734,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k2_tarski(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_371,c_549])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_157])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK0))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_376,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_741,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_376])).

cnf(c_20,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_937,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_20,c_21])).

cnf(c_548,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK5,X0_45) = k2_tarski(sK5,X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_371,c_375])).

cnf(c_625,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k2_tarski(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_372,c_548])).

cnf(c_675,plain,
    ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_376])).

cnf(c_880,plain,
    ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_20,c_21])).

cnf(c_735,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_372,c_549])).

cnf(c_812,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_376])).

cnf(c_874,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_20])).

cnf(c_624,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_371,c_548])).

cnf(c_672,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_376])).

cnf(c_815,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_21])).

cnf(c_5,negated_conjecture,
    ( k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_257,negated_conjecture,
    ( k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_255,negated_conjecture,
    ( sK2 = sK4 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_256,negated_conjecture,
    ( sK3 = sK5 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_391,plain,
    ( k13_lattice3(sK1,sK4,sK5) != k13_lattice3(sK0,sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_257,c_255,c_256])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_251,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_374,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_388,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_374,c_255])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_252,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_373,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_385,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_373,c_256])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.08/0.28  % Computer   : n004.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 13:39:08 EST 2020
% 0.13/0.28  % CPUTime    : 
% 0.13/0.28  % Running in FOF mode
% 0.76/0.86  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.76/0.86  
% 0.76/0.86  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.76/0.86  
% 0.76/0.86  ------  iProver source info
% 0.76/0.86  
% 0.76/0.86  git: date: 2020-06-30 10:37:57 +0100
% 0.76/0.86  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.76/0.86  git: non_committed_changes: false
% 0.76/0.86  git: last_make_outside_of_git: false
% 0.76/0.86  
% 0.76/0.86  ------ 
% 0.76/0.86  
% 0.76/0.86  ------ Input Options
% 0.76/0.86  
% 0.76/0.86  --out_options                           all
% 0.76/0.86  --tptp_safe_out                         true
% 0.76/0.86  --problem_path                          ""
% 0.76/0.86  --include_path                          ""
% 0.76/0.86  --clausifier                            res/vclausify_rel
% 0.76/0.86  --clausifier_options                    --mode clausify
% 0.76/0.86  --stdin                                 false
% 0.76/0.86  --stats_out                             all
% 0.76/0.86  
% 0.76/0.86  ------ General Options
% 0.76/0.86  
% 0.76/0.86  --fof                                   false
% 0.76/0.86  --time_out_real                         305.
% 0.76/0.86  --time_out_virtual                      -1.
% 0.76/0.86  --symbol_type_check                     false
% 0.76/0.86  --clausify_out                          false
% 0.76/0.86  --sig_cnt_out                           false
% 0.76/0.86  --trig_cnt_out                          false
% 0.76/0.86  --trig_cnt_out_tolerance                1.
% 0.76/0.86  --trig_cnt_out_sk_spl                   false
% 0.76/0.86  --abstr_cl_out                          false
% 0.76/0.86  
% 0.76/0.86  ------ Global Options
% 0.76/0.86  
% 0.76/0.86  --schedule                              default
% 0.76/0.86  --add_important_lit                     false
% 0.76/0.86  --prop_solver_per_cl                    1000
% 0.76/0.86  --min_unsat_core                        false
% 0.76/0.86  --soft_assumptions                      false
% 0.76/0.86  --soft_lemma_size                       3
% 0.76/0.86  --prop_impl_unit_size                   0
% 0.76/0.86  --prop_impl_unit                        []
% 0.76/0.86  --share_sel_clauses                     true
% 0.76/0.86  --reset_solvers                         false
% 0.76/0.86  --bc_imp_inh                            [conj_cone]
% 0.76/0.86  --conj_cone_tolerance                   3.
% 0.76/0.86  --extra_neg_conj                        none
% 0.76/0.86  --large_theory_mode                     true
% 0.76/0.86  --prolific_symb_bound                   200
% 0.76/0.86  --lt_threshold                          2000
% 0.76/0.86  --clause_weak_htbl                      true
% 0.76/0.86  --gc_record_bc_elim                     false
% 0.76/0.86  
% 0.76/0.86  ------ Preprocessing Options
% 0.76/0.86  
% 0.76/0.86  --preprocessing_flag                    true
% 0.76/0.86  --time_out_prep_mult                    0.1
% 0.76/0.86  --splitting_mode                        input
% 0.76/0.86  --splitting_grd                         true
% 0.76/0.86  --splitting_cvd                         false
% 0.76/0.86  --splitting_cvd_svl                     false
% 0.76/0.86  --splitting_nvd                         32
% 0.76/0.86  --sub_typing                            true
% 0.76/0.86  --prep_gs_sim                           true
% 0.76/0.86  --prep_unflatten                        true
% 0.76/0.86  --prep_res_sim                          true
% 0.76/0.86  --prep_upred                            true
% 0.76/0.86  --prep_sem_filter                       exhaustive
% 0.76/0.86  --prep_sem_filter_out                   false
% 0.76/0.86  --pred_elim                             true
% 0.76/0.86  --res_sim_input                         true
% 0.76/0.86  --eq_ax_congr_red                       true
% 0.76/0.86  --pure_diseq_elim                       true
% 0.76/0.86  --brand_transform                       false
% 0.76/0.86  --non_eq_to_eq                          false
% 0.76/0.86  --prep_def_merge                        true
% 0.76/0.86  --prep_def_merge_prop_impl              false
% 0.76/0.86  --prep_def_merge_mbd                    true
% 0.76/0.86  --prep_def_merge_tr_red                 false
% 0.76/0.86  --prep_def_merge_tr_cl                  false
% 0.76/0.86  --smt_preprocessing                     true
% 0.76/0.86  --smt_ac_axioms                         fast
% 0.76/0.86  --preprocessed_out                      false
% 0.76/0.86  --preprocessed_stats                    false
% 0.76/0.86  
% 0.76/0.86  ------ Abstraction refinement Options
% 0.76/0.86  
% 0.76/0.86  --abstr_ref                             []
% 0.76/0.86  --abstr_ref_prep                        false
% 0.76/0.86  --abstr_ref_until_sat                   false
% 0.76/0.86  --abstr_ref_sig_restrict                funpre
% 0.76/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 0.76/0.86  --abstr_ref_under                       []
% 0.76/0.86  
% 0.76/0.86  ------ SAT Options
% 0.76/0.86  
% 0.76/0.86  --sat_mode                              false
% 0.76/0.86  --sat_fm_restart_options                ""
% 0.76/0.86  --sat_gr_def                            false
% 0.76/0.86  --sat_epr_types                         true
% 0.76/0.86  --sat_non_cyclic_types                  false
% 0.76/0.86  --sat_finite_models                     false
% 0.76/0.86  --sat_fm_lemmas                         false
% 0.76/0.86  --sat_fm_prep                           false
% 0.76/0.86  --sat_fm_uc_incr                        true
% 0.76/0.86  --sat_out_model                         small
% 0.76/0.86  --sat_out_clauses                       false
% 0.76/0.86  
% 0.76/0.86  ------ QBF Options
% 0.76/0.86  
% 0.76/0.86  --qbf_mode                              false
% 0.76/0.86  --qbf_elim_univ                         false
% 0.76/0.86  --qbf_dom_inst                          none
% 0.76/0.86  --qbf_dom_pre_inst                      false
% 0.76/0.86  --qbf_sk_in                             false
% 0.76/0.86  --qbf_pred_elim                         true
% 0.76/0.86  --qbf_split                             512
% 0.76/0.86  
% 0.76/0.86  ------ BMC1 Options
% 0.76/0.86  
% 0.76/0.86  --bmc1_incremental                      false
% 0.76/0.86  --bmc1_axioms                           reachable_all
% 0.76/0.86  --bmc1_min_bound                        0
% 0.76/0.86  --bmc1_max_bound                        -1
% 0.76/0.86  --bmc1_max_bound_default                -1
% 0.76/0.86  --bmc1_symbol_reachability              true
% 0.76/0.86  --bmc1_property_lemmas                  false
% 0.76/0.86  --bmc1_k_induction                      false
% 0.76/0.86  --bmc1_non_equiv_states                 false
% 0.76/0.86  --bmc1_deadlock                         false
% 0.76/0.86  --bmc1_ucm                              false
% 0.76/0.86  --bmc1_add_unsat_core                   none
% 0.76/0.86  --bmc1_unsat_core_children              false
% 0.76/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 0.76/0.86  --bmc1_out_stat                         full
% 0.76/0.86  --bmc1_ground_init                      false
% 0.76/0.86  --bmc1_pre_inst_next_state              false
% 0.76/0.86  --bmc1_pre_inst_state                   false
% 0.76/0.86  --bmc1_pre_inst_reach_state             false
% 0.76/0.86  --bmc1_out_unsat_core                   false
% 0.76/0.86  --bmc1_aig_witness_out                  false
% 0.76/0.86  --bmc1_verbose                          false
% 0.76/0.86  --bmc1_dump_clauses_tptp                false
% 0.76/0.86  --bmc1_dump_unsat_core_tptp             false
% 0.76/0.86  --bmc1_dump_file                        -
% 0.76/0.86  --bmc1_ucm_expand_uc_limit              128
% 0.76/0.86  --bmc1_ucm_n_expand_iterations          6
% 0.76/0.86  --bmc1_ucm_extend_mode                  1
% 0.76/0.86  --bmc1_ucm_init_mode                    2
% 0.76/0.86  --bmc1_ucm_cone_mode                    none
% 0.76/0.86  --bmc1_ucm_reduced_relation_type        0
% 0.76/0.86  --bmc1_ucm_relax_model                  4
% 0.76/0.86  --bmc1_ucm_full_tr_after_sat            true
% 0.76/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 0.76/0.86  --bmc1_ucm_layered_model                none
% 0.76/0.86  --bmc1_ucm_max_lemma_size               10
% 0.76/0.86  
% 0.76/0.86  ------ AIG Options
% 0.76/0.86  
% 0.76/0.86  --aig_mode                              false
% 0.76/0.86  
% 0.76/0.86  ------ Instantiation Options
% 0.76/0.86  
% 0.76/0.86  --instantiation_flag                    true
% 0.76/0.86  --inst_sos_flag                         false
% 0.76/0.86  --inst_sos_phase                        true
% 0.76/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.76/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.76/0.86  --inst_lit_sel_side                     num_symb
% 0.76/0.86  --inst_solver_per_active                1400
% 0.76/0.86  --inst_solver_calls_frac                1.
% 0.76/0.86  --inst_passive_queue_type               priority_queues
% 0.76/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.76/0.86  --inst_passive_queues_freq              [25;2]
% 0.76/0.86  --inst_dismatching                      true
% 0.76/0.86  --inst_eager_unprocessed_to_passive     true
% 0.76/0.86  --inst_prop_sim_given                   true
% 0.76/0.86  --inst_prop_sim_new                     false
% 0.76/0.86  --inst_subs_new                         false
% 0.76/0.86  --inst_eq_res_simp                      false
% 0.76/0.86  --inst_subs_given                       false
% 0.76/0.86  --inst_orphan_elimination               true
% 0.76/0.86  --inst_learning_loop_flag               true
% 0.76/0.86  --inst_learning_start                   3000
% 0.76/0.86  --inst_learning_factor                  2
% 0.76/0.86  --inst_start_prop_sim_after_learn       3
% 0.76/0.86  --inst_sel_renew                        solver
% 0.76/0.86  --inst_lit_activity_flag                true
% 0.76/0.86  --inst_restr_to_given                   false
% 0.76/0.86  --inst_activity_threshold               500
% 0.76/0.86  --inst_out_proof                        true
% 0.76/0.86  
% 0.76/0.86  ------ Resolution Options
% 0.76/0.86  
% 0.76/0.86  --resolution_flag                       true
% 0.76/0.86  --res_lit_sel                           adaptive
% 0.76/0.86  --res_lit_sel_side                      none
% 0.76/0.86  --res_ordering                          kbo
% 0.76/0.86  --res_to_prop_solver                    active
% 0.76/0.86  --res_prop_simpl_new                    false
% 0.76/0.86  --res_prop_simpl_given                  true
% 0.76/0.86  --res_passive_queue_type                priority_queues
% 0.76/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.76/0.86  --res_passive_queues_freq               [15;5]
% 0.76/0.86  --res_forward_subs                      full
% 0.76/0.86  --res_backward_subs                     full
% 0.76/0.86  --res_forward_subs_resolution           true
% 0.76/0.86  --res_backward_subs_resolution          true
% 0.76/0.86  --res_orphan_elimination                true
% 0.76/0.86  --res_time_limit                        2.
% 0.76/0.86  --res_out_proof                         true
% 0.76/0.86  
% 0.76/0.86  ------ Superposition Options
% 0.76/0.86  
% 0.76/0.86  --superposition_flag                    true
% 0.76/0.86  --sup_passive_queue_type                priority_queues
% 0.76/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.76/0.86  --sup_passive_queues_freq               [8;1;4]
% 0.76/0.86  --demod_completeness_check              fast
% 0.76/0.86  --demod_use_ground                      true
% 0.76/0.86  --sup_to_prop_solver                    passive
% 0.76/0.86  --sup_prop_simpl_new                    true
% 0.76/0.86  --sup_prop_simpl_given                  true
% 0.76/0.86  --sup_fun_splitting                     false
% 0.76/0.86  --sup_smt_interval                      50000
% 0.76/0.86  
% 0.76/0.86  ------ Superposition Simplification Setup
% 0.76/0.86  
% 0.76/0.86  --sup_indices_passive                   []
% 0.76/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 0.76/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.86  --sup_full_bw                           [BwDemod]
% 0.76/0.86  --sup_immed_triv                        [TrivRules]
% 0.76/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.76/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.86  --sup_immed_bw_main                     []
% 0.76/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 0.76/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.86  
% 0.76/0.86  ------ Combination Options
% 0.76/0.86  
% 0.76/0.86  --comb_res_mult                         3
% 0.76/0.86  --comb_sup_mult                         2
% 0.76/0.86  --comb_inst_mult                        10
% 0.76/0.86  
% 0.76/0.86  ------ Debug Options
% 0.76/0.86  
% 0.76/0.86  --dbg_backtrace                         false
% 0.76/0.86  --dbg_dump_prop_clauses                 false
% 0.76/0.86  --dbg_dump_prop_clauses_file            -
% 0.76/0.86  --dbg_out_stat                          false
% 0.76/0.86  ------ Parsing...
% 0.76/0.86  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.76/0.86  
% 0.76/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.76/0.86  
% 0.76/0.86  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.76/0.86  
% 0.76/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.76/0.86  ------ Proving...
% 0.76/0.86  ------ Problem Properties 
% 0.76/0.86  
% 0.76/0.86  
% 0.76/0.86  clauses                                 9
% 0.76/0.86  conjectures                             7
% 0.76/0.86  EPR                                     2
% 0.76/0.86  Horn                                    9
% 0.76/0.86  unary                                   7
% 0.76/0.86  binary                                  0
% 0.76/0.86  lits                                    13
% 0.76/0.86  lits eq                                 4
% 0.76/0.86  fd_pure                                 0
% 0.76/0.86  fd_pseudo                               0
% 0.76/0.86  fd_cond                                 0
% 0.76/0.86  fd_pseudo_cond                          0
% 0.76/0.86  AC symbols                              0
% 0.76/0.86  
% 0.76/0.86  ------ Schedule dynamic 5 is on 
% 0.76/0.86  
% 0.76/0.86  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.76/0.86  
% 0.76/0.86  
% 0.76/0.86  ------ 
% 0.76/0.86  Current options:
% 0.76/0.86  ------ 
% 0.76/0.86  
% 0.76/0.86  ------ Input Options
% 0.76/0.86  
% 0.76/0.86  --out_options                           all
% 0.76/0.86  --tptp_safe_out                         true
% 0.76/0.86  --problem_path                          ""
% 0.76/0.86  --include_path                          ""
% 0.76/0.86  --clausifier                            res/vclausify_rel
% 0.76/0.86  --clausifier_options                    --mode clausify
% 0.76/0.86  --stdin                                 false
% 0.76/0.86  --stats_out                             all
% 0.76/0.87  
% 0.76/0.87  ------ General Options
% 0.76/0.87  
% 0.76/0.87  --fof                                   false
% 0.76/0.87  --time_out_real                         305.
% 0.76/0.87  --time_out_virtual                      -1.
% 0.76/0.87  --symbol_type_check                     false
% 0.76/0.87  --clausify_out                          false
% 0.76/0.87  --sig_cnt_out                           false
% 0.76/0.87  --trig_cnt_out                          false
% 0.76/0.87  --trig_cnt_out_tolerance                1.
% 0.76/0.87  --trig_cnt_out_sk_spl                   false
% 0.76/0.87  --abstr_cl_out                          false
% 0.76/0.87  
% 0.76/0.87  ------ Global Options
% 0.76/0.87  
% 0.76/0.87  --schedule                              default
% 0.76/0.87  --add_important_lit                     false
% 0.76/0.87  --prop_solver_per_cl                    1000
% 0.76/0.87  --min_unsat_core                        false
% 0.76/0.87  --soft_assumptions                      false
% 0.76/0.87  --soft_lemma_size                       3
% 0.76/0.87  --prop_impl_unit_size                   0
% 0.76/0.87  --prop_impl_unit                        []
% 0.76/0.87  --share_sel_clauses                     true
% 0.76/0.87  --reset_solvers                         false
% 0.76/0.87  --bc_imp_inh                            [conj_cone]
% 0.76/0.87  --conj_cone_tolerance                   3.
% 0.76/0.87  --extra_neg_conj                        none
% 0.76/0.87  --large_theory_mode                     true
% 0.76/0.87  --prolific_symb_bound                   200
% 0.76/0.87  --lt_threshold                          2000
% 0.76/0.87  --clause_weak_htbl                      true
% 0.76/0.87  --gc_record_bc_elim                     false
% 0.76/0.87  
% 0.76/0.87  ------ Preprocessing Options
% 0.76/0.87  
% 0.76/0.87  --preprocessing_flag                    true
% 0.76/0.87  --time_out_prep_mult                    0.1
% 0.76/0.87  --splitting_mode                        input
% 0.76/0.87  --splitting_grd                         true
% 0.76/0.87  --splitting_cvd                         false
% 0.76/0.87  --splitting_cvd_svl                     false
% 0.76/0.87  --splitting_nvd                         32
% 0.76/0.87  --sub_typing                            true
% 0.76/0.87  --prep_gs_sim                           true
% 0.76/0.87  --prep_unflatten                        true
% 0.76/0.87  --prep_res_sim                          true
% 0.76/0.87  --prep_upred                            true
% 0.76/0.87  --prep_sem_filter                       exhaustive
% 0.76/0.87  --prep_sem_filter_out                   false
% 0.76/0.87  --pred_elim                             true
% 0.76/0.87  --res_sim_input                         true
% 0.76/0.87  --eq_ax_congr_red                       true
% 0.76/0.87  --pure_diseq_elim                       true
% 0.76/0.87  --brand_transform                       false
% 0.76/0.87  --non_eq_to_eq                          false
% 0.76/0.87  --prep_def_merge                        true
% 0.76/0.87  --prep_def_merge_prop_impl              false
% 0.76/0.87  --prep_def_merge_mbd                    true
% 0.76/0.87  --prep_def_merge_tr_red                 false
% 0.76/0.87  --prep_def_merge_tr_cl                  false
% 0.76/0.87  --smt_preprocessing                     true
% 0.76/0.87  --smt_ac_axioms                         fast
% 0.76/0.87  --preprocessed_out                      false
% 0.76/0.87  --preprocessed_stats                    false
% 0.76/0.87  
% 0.76/0.87  ------ Abstraction refinement Options
% 0.76/0.87  
% 0.76/0.87  --abstr_ref                             []
% 0.76/0.87  --abstr_ref_prep                        false
% 0.76/0.87  --abstr_ref_until_sat                   false
% 0.76/0.87  --abstr_ref_sig_restrict                funpre
% 0.76/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 0.76/0.87  --abstr_ref_under                       []
% 0.76/0.87  
% 0.76/0.87  ------ SAT Options
% 0.76/0.87  
% 0.76/0.87  --sat_mode                              false
% 0.76/0.87  --sat_fm_restart_options                ""
% 0.76/0.87  --sat_gr_def                            false
% 0.76/0.87  --sat_epr_types                         true
% 0.76/0.87  --sat_non_cyclic_types                  false
% 0.76/0.87  --sat_finite_models                     false
% 0.76/0.87  --sat_fm_lemmas                         false
% 0.76/0.87  --sat_fm_prep                           false
% 0.76/0.87  --sat_fm_uc_incr                        true
% 0.76/0.87  --sat_out_model                         small
% 0.76/0.87  --sat_out_clauses                       false
% 0.76/0.87  
% 0.76/0.87  ------ QBF Options
% 0.76/0.87  
% 0.76/0.87  --qbf_mode                              false
% 0.76/0.87  --qbf_elim_univ                         false
% 0.76/0.87  --qbf_dom_inst                          none
% 0.76/0.87  --qbf_dom_pre_inst                      false
% 0.76/0.87  --qbf_sk_in                             false
% 0.76/0.87  --qbf_pred_elim                         true
% 0.76/0.87  --qbf_split                             512
% 0.76/0.87  
% 0.76/0.87  ------ BMC1 Options
% 0.76/0.87  
% 0.76/0.87  --bmc1_incremental                      false
% 0.76/0.87  --bmc1_axioms                           reachable_all
% 0.76/0.87  --bmc1_min_bound                        0
% 0.76/0.87  --bmc1_max_bound                        -1
% 0.76/0.87  --bmc1_max_bound_default                -1
% 0.76/0.87  --bmc1_symbol_reachability              true
% 0.76/0.87  --bmc1_property_lemmas                  false
% 0.76/0.87  --bmc1_k_induction                      false
% 0.76/0.87  --bmc1_non_equiv_states                 false
% 0.76/0.87  --bmc1_deadlock                         false
% 0.76/0.87  --bmc1_ucm                              false
% 0.76/0.87  --bmc1_add_unsat_core                   none
% 0.76/0.87  --bmc1_unsat_core_children              false
% 0.76/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 0.76/0.87  --bmc1_out_stat                         full
% 0.76/0.87  --bmc1_ground_init                      false
% 0.76/0.87  --bmc1_pre_inst_next_state              false
% 0.76/0.87  --bmc1_pre_inst_state                   false
% 0.76/0.87  --bmc1_pre_inst_reach_state             false
% 0.76/0.87  --bmc1_out_unsat_core                   false
% 0.76/0.87  --bmc1_aig_witness_out                  false
% 0.76/0.87  --bmc1_verbose                          false
% 0.76/0.87  --bmc1_dump_clauses_tptp                false
% 0.76/0.87  --bmc1_dump_unsat_core_tptp             false
% 0.76/0.87  --bmc1_dump_file                        -
% 0.76/0.87  --bmc1_ucm_expand_uc_limit              128
% 0.76/0.87  --bmc1_ucm_n_expand_iterations          6
% 0.76/0.87  --bmc1_ucm_extend_mode                  1
% 0.76/0.87  --bmc1_ucm_init_mode                    2
% 0.76/0.87  --bmc1_ucm_cone_mode                    none
% 0.76/0.87  --bmc1_ucm_reduced_relation_type        0
% 0.76/0.87  --bmc1_ucm_relax_model                  4
% 0.76/0.87  --bmc1_ucm_full_tr_after_sat            true
% 0.76/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 0.76/0.87  --bmc1_ucm_layered_model                none
% 0.76/0.87  --bmc1_ucm_max_lemma_size               10
% 0.76/0.87  
% 0.76/0.87  ------ AIG Options
% 0.76/0.87  
% 0.76/0.87  --aig_mode                              false
% 0.76/0.87  
% 0.76/0.87  ------ Instantiation Options
% 0.76/0.87  
% 0.76/0.87  --instantiation_flag                    true
% 0.76/0.87  --inst_sos_flag                         false
% 0.76/0.87  --inst_sos_phase                        true
% 0.76/0.87  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.76/0.87  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.76/0.87  --inst_lit_sel_side                     none
% 0.76/0.87  --inst_solver_per_active                1400
% 0.76/0.87  --inst_solver_calls_frac                1.
% 0.76/0.87  --inst_passive_queue_type               priority_queues
% 0.76/0.87  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.76/0.87  --inst_passive_queues_freq              [25;2]
% 0.76/0.87  --inst_dismatching                      true
% 0.76/0.87  --inst_eager_unprocessed_to_passive     true
% 0.76/0.87  --inst_prop_sim_given                   true
% 0.76/0.87  --inst_prop_sim_new                     false
% 0.76/0.87  --inst_subs_new                         false
% 0.76/0.87  --inst_eq_res_simp                      false
% 0.76/0.87  --inst_subs_given                       false
% 0.76/0.87  --inst_orphan_elimination               true
% 0.76/0.87  --inst_learning_loop_flag               true
% 0.76/0.87  --inst_learning_start                   3000
% 0.76/0.87  --inst_learning_factor                  2
% 0.76/0.87  --inst_start_prop_sim_after_learn       3
% 0.76/0.87  --inst_sel_renew                        solver
% 0.76/0.87  --inst_lit_activity_flag                true
% 0.76/0.87  --inst_restr_to_given                   false
% 0.76/0.87  --inst_activity_threshold               500
% 0.76/0.87  --inst_out_proof                        true
% 0.76/0.87  
% 0.76/0.87  ------ Resolution Options
% 0.76/0.87  
% 0.76/0.87  --resolution_flag                       false
% 0.76/0.87  --res_lit_sel                           adaptive
% 0.76/0.87  --res_lit_sel_side                      none
% 0.76/0.87  --res_ordering                          kbo
% 0.76/0.87  --res_to_prop_solver                    active
% 0.76/0.87  --res_prop_simpl_new                    false
% 0.76/0.87  --res_prop_simpl_given                  true
% 0.76/0.87  --res_passive_queue_type                priority_queues
% 0.76/0.87  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.76/0.87  --res_passive_queues_freq               [15;5]
% 0.76/0.87  --res_forward_subs                      full
% 0.76/0.87  --res_backward_subs                     full
% 0.76/0.87  --res_forward_subs_resolution           true
% 0.76/0.87  --res_backward_subs_resolution          true
% 0.76/0.87  --res_orphan_elimination                true
% 0.76/0.87  --res_time_limit                        2.
% 0.76/0.87  --res_out_proof                         true
% 0.76/0.87  
% 0.76/0.87  ------ Superposition Options
% 0.76/0.87  
% 0.76/0.87  --superposition_flag                    true
% 0.76/0.87  --sup_passive_queue_type                priority_queues
% 0.76/0.87  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.76/0.87  --sup_passive_queues_freq               [8;1;4]
% 0.76/0.87  --demod_completeness_check              fast
% 0.76/0.87  --demod_use_ground                      true
% 0.76/0.87  --sup_to_prop_solver                    passive
% 0.76/0.87  --sup_prop_simpl_new                    true
% 0.76/0.87  --sup_prop_simpl_given                  true
% 0.76/0.87  --sup_fun_splitting                     false
% 0.76/0.87  --sup_smt_interval                      50000
% 0.76/0.87  
% 0.76/0.87  ------ Superposition Simplification Setup
% 0.76/0.87  
% 0.76/0.87  --sup_indices_passive                   []
% 0.76/0.87  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.87  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.87  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.76/0.87  --sup_full_triv                         [TrivRules;PropSubs]
% 0.76/0.87  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.87  --sup_full_bw                           [BwDemod]
% 0.76/0.87  --sup_immed_triv                        [TrivRules]
% 0.76/0.87  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.76/0.87  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.87  --sup_immed_bw_main                     []
% 0.76/0.87  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.87  --sup_input_triv                        [Unflattening;TrivRules]
% 0.76/0.87  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.76/0.87  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.76/0.87  
% 0.76/0.87  ------ Combination Options
% 0.76/0.87  
% 0.76/0.87  --comb_res_mult                         3
% 0.76/0.87  --comb_sup_mult                         2
% 0.76/0.87  --comb_inst_mult                        10
% 0.76/0.87  
% 0.76/0.87  ------ Debug Options
% 0.76/0.87  
% 0.76/0.87  --dbg_backtrace                         false
% 0.76/0.87  --dbg_dump_prop_clauses                 false
% 0.76/0.87  --dbg_dump_prop_clauses_file            -
% 0.76/0.87  --dbg_out_stat                          false
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  ------ Proving...
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  % SZS status CounterSatisfiable for theBenchmark.p
% 0.76/0.87  
% 0.76/0.87  % SZS output start Saturation for theBenchmark.p
% 0.76/0.87  
% 0.76/0.87  fof(f7,conjecture,(
% 0.76/0.87    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f8,negated_conjecture,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(negated_conjecture,[],[f7])).
% 0.76/0.87  
% 0.76/0.87  fof(f9,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((v6_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f8])).
% 0.76/0.87  
% 0.76/0.87  fof(f10,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : ((v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f9])).
% 0.76/0.87  
% 0.76/0.87  fof(f11,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f10])).
% 0.76/0.87  
% 0.76/0.87  fof(f12,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f11])).
% 0.76/0.87  
% 0.76/0.87  fof(f13,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f12])).
% 0.76/0.87  
% 0.76/0.87  fof(f14,plain,(
% 0.76/0.87    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((X3 = X5 & X2 = X4) => k13_lattice3(X0,X4,X5) = k13_lattice3(X1,X2,X3))))))))),
% 0.76/0.87    inference(pure_predicate_removal,[],[f13])).
% 0.76/0.87  
% 0.76/0.87  fof(f25,plain,(
% 0.76/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & (X3 = X5 & X2 = X4)) & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & (l1_orders_2(X0) & v1_lattice3(X0)))),
% 0.76/0.87    inference(ennf_transformation,[],[f14])).
% 0.76/0.87  
% 0.76/0.87  fof(f26,plain,(
% 0.76/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & v1_lattice3(X0))),
% 0.76/0.87    inference(flattening,[],[f25])).
% 0.76/0.87  
% 0.76/0.87  fof(f32,plain,(
% 0.76/0.87    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) => (k13_lattice3(X0,X4,sK5) != k13_lattice3(X1,X2,X3) & sK5 = X3 & X2 = X4 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f31,plain,(
% 0.76/0.87    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) => (? [X5] : (k13_lattice3(X0,sK4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & sK4 = X2 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f30,plain,(
% 0.76/0.87    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (? [X5] : (k13_lattice3(X1,X2,sK3) != k13_lattice3(X0,X4,X5) & sK3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f29,plain,(
% 0.76/0.87    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X1,sK2,X3) != k13_lattice3(X0,X4,X5) & X3 = X5 & sK2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK2,u1_struct_0(X1)))) )),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f28,plain,(
% 0.76/0.87    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(sK1,X2,X3) != k13_lattice3(X0,X4,X5) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,u1_struct_0(sK1))) & ~v2_struct_0(sK1))) )),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f27,plain,(
% 0.76/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(X0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & v1_lattice3(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k13_lattice3(sK0,X4,X5) != k13_lattice3(X1,X2,X3) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(sK0))) & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & v1_lattice3(sK0))),
% 0.76/0.87    introduced(choice_axiom,[])).
% 0.76/0.87  
% 0.76/0.87  fof(f33,plain,(
% 0.76/0.87    (((((k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) & sK3 = sK5 & sK2 = sK4 & m1_subset_1(sK5,u1_struct_0(sK0))) & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & v1_lattice3(sK0)),
% 0.76/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f32,f31,f30,f29,f28,f27])).
% 0.76/0.87  
% 0.76/0.87  fof(f45,plain,(
% 0.76/0.87    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f44,plain,(
% 0.76/0.87    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f5,axiom,(
% 0.76/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f21,plain,(
% 0.76/0.87    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.76/0.87    inference(ennf_transformation,[],[f5])).
% 0.76/0.87  
% 0.76/0.87  fof(f22,plain,(
% 0.76/0.87    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.76/0.87    inference(flattening,[],[f21])).
% 0.76/0.87  
% 0.76/0.87  fof(f37,plain,(
% 0.76/0.87    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.76/0.87    inference(cnf_transformation,[],[f22])).
% 0.76/0.87  
% 0.76/0.87  fof(f2,axiom,(
% 0.76/0.87    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f16,plain,(
% 0.76/0.87    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.76/0.87    inference(ennf_transformation,[],[f2])).
% 0.76/0.87  
% 0.76/0.87  fof(f17,plain,(
% 0.76/0.87    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.76/0.87    inference(flattening,[],[f16])).
% 0.76/0.87  
% 0.76/0.87  fof(f34,plain,(
% 0.76/0.87    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.76/0.87    inference(cnf_transformation,[],[f17])).
% 0.76/0.87  
% 0.76/0.87  fof(f4,axiom,(
% 0.76/0.87    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f20,plain,(
% 0.76/0.87    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.76/0.87    inference(ennf_transformation,[],[f4])).
% 0.76/0.87  
% 0.76/0.87  fof(f36,plain,(
% 0.76/0.87    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.76/0.87    inference(cnf_transformation,[],[f20])).
% 0.76/0.87  
% 0.76/0.87  fof(f40,plain,(
% 0.76/0.87    l1_orders_2(sK0)),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f39,plain,(
% 0.76/0.87    v1_lattice3(sK0)),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f6,axiom,(
% 0.76/0.87    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f23,plain,(
% 0.76/0.87    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.76/0.87    inference(ennf_transformation,[],[f6])).
% 0.76/0.87  
% 0.76/0.87  fof(f24,plain,(
% 0.76/0.87    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.76/0.87    inference(flattening,[],[f23])).
% 0.76/0.87  
% 0.76/0.87  fof(f38,plain,(
% 0.76/0.87    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.76/0.87    inference(cnf_transformation,[],[f24])).
% 0.76/0.87  
% 0.76/0.87  fof(f3,axiom,(
% 0.76/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.76/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.76/0.87  
% 0.76/0.87  fof(f18,plain,(
% 0.76/0.87    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.76/0.87    inference(ennf_transformation,[],[f3])).
% 0.76/0.87  
% 0.76/0.87  fof(f19,plain,(
% 0.76/0.87    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.76/0.87    inference(flattening,[],[f18])).
% 0.76/0.87  
% 0.76/0.87  fof(f35,plain,(
% 0.76/0.87    ( ! [X2,X0,X1] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.76/0.87    inference(cnf_transformation,[],[f19])).
% 0.76/0.87  
% 0.76/0.87  fof(f48,plain,(
% 0.76/0.87    k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3)),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f46,plain,(
% 0.76/0.87    sK2 = sK4),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f47,plain,(
% 0.76/0.87    sK3 = sK5),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f42,plain,(
% 0.76/0.87    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  fof(f43,plain,(
% 0.76/0.87    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.76/0.87    inference(cnf_transformation,[],[f33])).
% 0.76/0.87  
% 0.76/0.87  cnf(c_118,plain,
% 0.76/0.87      ( ~ v1_lattice3(X0) | v1_lattice3(X1) | X1 != X0 ),
% 0.76/0.87      theory(equality) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_117,plain,
% 0.76/0.87      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 0.76/0.87      theory(equality) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_115,plain,
% 0.76/0.87      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 0.76/0.87      theory(equality) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_114,plain,
% 0.76/0.87      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.76/0.87      theory(equality) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_258,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_8,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 0.76/0.87      inference(cnf_transformation,[],[f45]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_254,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_8]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_371,plain,
% 0.76/0.87      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_9,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
% 0.76/0.87      inference(cnf_transformation,[],[f44]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_253,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_9]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_372,plain,
% 0.76/0.87      ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_3,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,X1)
% 0.76/0.87      | ~ m1_subset_1(X2,X1)
% 0.76/0.87      | v1_xboole_0(X1)
% 0.76/0.87      | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
% 0.76/0.87      inference(cnf_transformation,[],[f37]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_0,plain,
% 0.76/0.87      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 0.76/0.87      inference(cnf_transformation,[],[f34]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_2,plain,
% 0.76/0.87      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 0.76/0.87      inference(cnf_transformation,[],[f36]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_13,negated_conjecture,
% 0.76/0.87      ( l1_orders_2(sK0) ),
% 0.76/0.87      inference(cnf_transformation,[],[f40]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_145,plain,
% 0.76/0.87      ( l1_struct_0(X0) | sK0 != X0 ),
% 0.76/0.87      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_146,plain,
% 0.76/0.87      ( l1_struct_0(sK0) ),
% 0.76/0.87      inference(unflattening,[status(thm)],[c_145]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_154,plain,
% 0.76/0.87      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 0.76/0.87      inference(resolution_lifted,[status(thm)],[c_0,c_146]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_155,plain,
% 0.76/0.87      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 0.76/0.87      inference(unflattening,[status(thm)],[c_154]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_14,negated_conjecture,
% 0.76/0.87      ( v1_lattice3(sK0) ),
% 0.76/0.87      inference(cnf_transformation,[],[f39]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_4,plain,
% 0.76/0.87      ( ~ v1_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 0.76/0.87      inference(cnf_transformation,[],[f38]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_23,plain,
% 0.76/0.87      ( ~ v1_lattice3(sK0) | ~ l1_orders_2(sK0) | ~ v2_struct_0(sK0) ),
% 0.76/0.87      inference(instantiation,[status(thm)],[c_4]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_29,plain,
% 0.76/0.87      ( ~ l1_orders_2(sK0) | l1_struct_0(sK0) ),
% 0.76/0.87      inference(instantiation,[status(thm)],[c_2]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_35,plain,
% 0.76/0.87      ( v2_struct_0(sK0)
% 0.76/0.87      | ~ l1_struct_0(sK0)
% 0.76/0.87      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 0.76/0.87      inference(instantiation,[status(thm)],[c_0]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_157,plain,
% 0.76/0.87      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 0.76/0.87      inference(global_propositional_subsumption,
% 0.76/0.87                [status(thm)],
% 0.76/0.87                [c_155,c_14,c_13,c_23,c_29,c_35]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_167,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,X1)
% 0.76/0.87      | ~ m1_subset_1(X2,X1)
% 0.76/0.87      | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
% 0.76/0.87      | u1_struct_0(sK0) != X1 ),
% 0.76/0.87      inference(resolution_lifted,[status(thm)],[c_3,c_157]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_168,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.76/0.87      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.76/0.87      | k7_domain_1(u1_struct_0(sK0),X0,X1) = k2_tarski(X0,X1) ),
% 0.76/0.87      inference(unflattening,[status(thm)],[c_167]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_250,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0_45,u1_struct_0(sK0))
% 0.76/0.87      | ~ m1_subset_1(X1_45,u1_struct_0(sK0))
% 0.76/0.87      | k7_domain_1(u1_struct_0(sK0),X0_45,X1_45) = k2_tarski(X0_45,X1_45) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_168]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_375,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),X0_45,X1_45) = k2_tarski(X0_45,X1_45)
% 0.76/0.87      | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top
% 0.76/0.87      | m1_subset_1(X1_45,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_549,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK4,X0_45) = k2_tarski(sK4,X0_45)
% 0.76/0.87      | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_372,c_375]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_734,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k2_tarski(sK4,sK5) ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_371,c_549]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_1,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,X1)
% 0.76/0.87      | ~ m1_subset_1(X2,X1)
% 0.76/0.87      | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
% 0.76/0.87      | v1_xboole_0(X1) ),
% 0.76/0.87      inference(cnf_transformation,[],[f35]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_182,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,X1)
% 0.76/0.87      | ~ m1_subset_1(X2,X1)
% 0.76/0.87      | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
% 0.76/0.87      | u1_struct_0(sK0) != X1 ),
% 0.76/0.87      inference(resolution_lifted,[status(thm)],[c_1,c_157]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_183,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.76/0.87      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.76/0.87      | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.76/0.87      inference(unflattening,[status(thm)],[c_182]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_249,plain,
% 0.76/0.87      ( ~ m1_subset_1(X0_45,u1_struct_0(sK0))
% 0.76/0.87      | ~ m1_subset_1(X1_45,u1_struct_0(sK0))
% 0.76/0.87      | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_183]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_376,plain,
% 0.76/0.87      ( m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top
% 0.76/0.87      | m1_subset_1(X1_45,u1_struct_0(sK0)) != iProver_top
% 0.76/0.87      | m1_subset_1(k7_domain_1(u1_struct_0(sK0),X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_741,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.76/0.87      | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top
% 0.76/0.87      | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_734,c_376]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_20,plain,
% 0.76/0.87      ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_21,plain,
% 0.76/0.87      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_937,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.76/0.87      inference(global_propositional_subsumption,
% 0.76/0.87                [status(thm)],
% 0.76/0.87                [c_741,c_20,c_21]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_548,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK5,X0_45) = k2_tarski(sK5,X0_45)
% 0.76/0.87      | m1_subset_1(X0_45,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_371,c_375]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_625,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k2_tarski(sK5,sK4) ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_372,c_548]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_675,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.76/0.87      | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top
% 0.76/0.87      | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_625,c_376]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_880,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.76/0.87      inference(global_propositional_subsumption,
% 0.76/0.87                [status(thm)],
% 0.76/0.87                [c_675,c_20,c_21]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_735,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k2_tarski(sK4,sK4) ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_372,c_549]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_812,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.76/0.87      | m1_subset_1(sK4,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_735,c_376]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_874,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.76/0.87      inference(global_propositional_subsumption,[status(thm)],[c_812,c_20]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_624,plain,
% 0.76/0.87      ( k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k2_tarski(sK5,sK5) ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_371,c_548]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_672,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.76/0.87      | m1_subset_1(sK5,u1_struct_0(sK0)) != iProver_top ),
% 0.76/0.87      inference(superposition,[status(thm)],[c_624,c_376]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_815,plain,
% 0.76/0.87      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.76/0.87      inference(global_propositional_subsumption,[status(thm)],[c_672,c_21]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_5,negated_conjecture,
% 0.76/0.87      ( k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) ),
% 0.76/0.87      inference(cnf_transformation,[],[f48]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_257,negated_conjecture,
% 0.76/0.87      ( k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK2,sK3) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_5]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_7,negated_conjecture,
% 0.76/0.87      ( sK2 = sK4 ),
% 0.76/0.87      inference(cnf_transformation,[],[f46]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_255,negated_conjecture,
% 0.76/0.87      ( sK2 = sK4 ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_7]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_6,negated_conjecture,
% 0.76/0.87      ( sK3 = sK5 ),
% 0.76/0.87      inference(cnf_transformation,[],[f47]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_256,negated_conjecture,
% 0.76/0.87      ( sK3 = sK5 ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_6]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_391,plain,
% 0.76/0.87      ( k13_lattice3(sK1,sK4,sK5) != k13_lattice3(sK0,sK4,sK5) ),
% 0.76/0.87      inference(light_normalisation,[status(thm)],[c_257,c_255,c_256]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_11,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.76/0.87      inference(cnf_transformation,[],[f42]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_251,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_11]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_374,plain,
% 0.76/0.87      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_388,plain,
% 0.76/0.87      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 0.76/0.87      inference(light_normalisation,[status(thm)],[c_374,c_255]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_10,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.76/0.87      inference(cnf_transformation,[],[f43]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_252,negated_conjecture,
% 0.76/0.87      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.76/0.87      inference(subtyping,[status(esa)],[c_10]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_373,plain,
% 0.76/0.87      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 0.76/0.87      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 0.76/0.87  
% 0.76/0.87  cnf(c_385,plain,
% 0.76/0.87      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 0.76/0.87      inference(light_normalisation,[status(thm)],[c_373,c_256]) ).
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  % SZS output end Saturation for theBenchmark.p
% 0.76/0.87  
% 0.76/0.87  ------                               Statistics
% 0.76/0.87  
% 0.76/0.87  ------ General
% 0.76/0.87  
% 0.76/0.87  abstr_ref_over_cycles:                  0
% 0.76/0.87  abstr_ref_under_cycles:                 0
% 0.76/0.87  gc_basic_clause_elim:                   0
% 0.76/0.87  forced_gc_time:                         0
% 0.76/0.87  parsing_time:                           0.007
% 0.76/0.87  unif_index_cands_time:                  0.
% 0.76/0.87  unif_index_add_time:                    0.
% 0.76/0.87  orderings_time:                         0.
% 0.76/0.87  out_proof_time:                         0.
% 0.76/0.87  total_time:                             0.054
% 0.76/0.87  num_of_symbols:                         52
% 0.76/0.87  num_of_terms:                           905
% 0.76/0.87  
% 0.76/0.87  ------ Preprocessing
% 0.76/0.87  
% 0.76/0.87  num_of_splits:                          0
% 0.76/0.87  num_of_split_atoms:                     0
% 0.76/0.87  num_of_reused_defs:                     0
% 0.76/0.87  num_eq_ax_congr_red:                    20
% 0.76/0.87  num_of_sem_filtered_clauses:            1
% 0.76/0.87  num_of_subtypes:                        4
% 0.76/0.87  monotx_restored_types:                  0
% 0.76/0.87  sat_num_of_epr_types:                   0
% 0.76/0.87  sat_num_of_non_cyclic_types:            0
% 0.76/0.87  sat_guarded_non_collapsed_types:        0
% 0.76/0.87  num_pure_diseq_elim:                    0
% 0.76/0.87  simp_replaced_by:                       0
% 0.76/0.87  res_preprocessed:                       55
% 0.76/0.87  prep_upred:                             0
% 0.76/0.87  prep_unflattend:                        5
% 0.76/0.87  smt_new_axioms:                         0
% 0.76/0.87  pred_elim_cands:                        1
% 0.76/0.87  pred_elim:                              5
% 0.76/0.87  pred_elim_cl:                           6
% 0.76/0.87  pred_elim_cycles:                       7
% 0.76/0.87  merged_defs:                            0
% 0.76/0.87  merged_defs_ncl:                        0
% 0.76/0.87  bin_hyper_res:                          0
% 0.76/0.87  prep_cycles:                            4
% 0.76/0.87  pred_elim_time:                         0.001
% 0.76/0.87  splitting_time:                         0.
% 0.76/0.87  sem_filter_time:                        0.
% 0.76/0.87  monotx_time:                            0.
% 0.76/0.87  subtype_inf_time:                       0.
% 0.76/0.87  
% 0.76/0.87  ------ Problem properties
% 0.76/0.87  
% 0.76/0.87  clauses:                                9
% 0.76/0.87  conjectures:                            7
% 0.76/0.87  epr:                                    2
% 0.76/0.87  horn:                                   9
% 0.76/0.87  ground:                                 7
% 0.76/0.87  unary:                                  7
% 0.76/0.87  binary:                                 0
% 0.76/0.87  lits:                                   13
% 0.76/0.87  lits_eq:                                4
% 0.76/0.87  fd_pure:                                0
% 0.76/0.87  fd_pseudo:                              0
% 0.76/0.87  fd_cond:                                0
% 0.76/0.87  fd_pseudo_cond:                         0
% 0.76/0.87  ac_symbols:                             0
% 0.76/0.87  
% 0.76/0.87  ------ Propositional Solver
% 0.76/0.87  
% 0.76/0.87  prop_solver_calls:                      28
% 0.76/0.87  prop_fast_solver_calls:                 236
% 0.76/0.87  smt_solver_calls:                       0
% 0.76/0.87  smt_fast_solver_calls:                  0
% 0.76/0.87  prop_num_of_clauses:                    335
% 0.76/0.87  prop_preprocess_simplified:             1306
% 0.76/0.87  prop_fo_subsumed:                       8
% 0.76/0.87  prop_solver_time:                       0.
% 0.76/0.87  smt_solver_time:                        0.
% 0.76/0.87  smt_fast_solver_time:                   0.
% 0.76/0.87  prop_fast_solver_time:                  0.
% 0.76/0.87  prop_unsat_core_time:                   0.
% 0.76/0.87  
% 0.76/0.87  ------ QBF
% 0.76/0.87  
% 0.76/0.87  qbf_q_res:                              0
% 0.76/0.87  qbf_num_tautologies:                    0
% 0.76/0.87  qbf_prep_cycles:                        0
% 0.76/0.87  
% 0.76/0.87  ------ BMC1
% 0.76/0.87  
% 0.76/0.87  bmc1_current_bound:                     -1
% 0.76/0.87  bmc1_last_solved_bound:                 -1
% 0.76/0.87  bmc1_unsat_core_size:                   -1
% 0.76/0.87  bmc1_unsat_core_parents_size:           -1
% 0.76/0.87  bmc1_merge_next_fun:                    0
% 0.76/0.87  bmc1_unsat_core_clauses_time:           0.
% 0.76/0.87  
% 0.76/0.87  ------ Instantiation
% 0.76/0.87  
% 0.76/0.87  inst_num_of_clauses:                    128
% 0.76/0.87  inst_num_in_passive:                    14
% 0.76/0.87  inst_num_in_active:                     92
% 0.76/0.87  inst_num_in_unprocessed:                23
% 0.76/0.87  inst_num_of_loops:                      100
% 0.76/0.87  inst_num_of_learning_restarts:          0
% 0.76/0.87  inst_num_moves_active_passive:          2
% 0.76/0.87  inst_lit_activity:                      0
% 0.76/0.87  inst_lit_activity_moves:                0
% 0.76/0.87  inst_num_tautologies:                   0
% 0.76/0.87  inst_num_prop_implied:                  0
% 0.76/0.87  inst_num_existing_simplified:           0
% 0.76/0.87  inst_num_eq_res_simplified:             0
% 0.76/0.87  inst_num_child_elim:                    0
% 0.76/0.87  inst_num_of_dismatching_blockings:      14
% 0.76/0.87  inst_num_of_non_proper_insts:           141
% 0.76/0.87  inst_num_of_duplicates:                 0
% 0.76/0.87  inst_inst_num_from_inst_to_res:         0
% 0.76/0.87  inst_dismatching_checking_time:         0.
% 0.76/0.87  
% 0.76/0.87  ------ Resolution
% 0.76/0.87  
% 0.76/0.87  res_num_of_clauses:                     0
% 0.76/0.87  res_num_in_passive:                     0
% 0.76/0.87  res_num_in_active:                      0
% 0.76/0.87  res_num_of_loops:                       59
% 0.76/0.87  res_forward_subset_subsumed:            28
% 0.76/0.87  res_backward_subset_subsumed:           6
% 0.76/0.87  res_forward_subsumed:                   0
% 0.76/0.87  res_backward_subsumed:                  0
% 0.76/0.87  res_forward_subsumption_resolution:     0
% 0.76/0.87  res_backward_subsumption_resolution:    0
% 0.76/0.87  res_clause_to_clause_subsumption:       20
% 0.76/0.87  res_orphan_elimination:                 0
% 0.76/0.87  res_tautology_del:                      36
% 0.76/0.87  res_num_eq_res_simplified:              0
% 0.76/0.87  res_num_sel_changes:                    0
% 0.76/0.87  res_moves_from_active_to_pass:          0
% 0.76/0.87  
% 0.76/0.87  ------ Superposition
% 0.76/0.87  
% 0.76/0.87  sup_time_total:                         0.
% 0.76/0.87  sup_time_generating:                    0.
% 0.76/0.87  sup_time_sim_full:                      0.
% 0.76/0.87  sup_time_sim_immed:                     0.
% 0.76/0.87  
% 0.76/0.87  sup_num_of_clauses:                     19
% 0.76/0.87  sup_num_in_active:                      19
% 0.76/0.87  sup_num_in_passive:                     0
% 0.76/0.87  sup_num_of_loops:                       19
% 0.76/0.87  sup_fw_superposition:                   6
% 0.76/0.87  sup_bw_superposition:                   4
% 0.76/0.87  sup_immediate_simplified:               0
% 0.76/0.87  sup_given_eliminated:                   0
% 0.76/0.87  comparisons_done:                       0
% 0.76/0.87  comparisons_avoided:                    0
% 0.76/0.87  
% 0.76/0.87  ------ Simplifications
% 0.76/0.87  
% 0.76/0.87  
% 0.76/0.87  sim_fw_subset_subsumed:                 0
% 0.76/0.87  sim_bw_subset_subsumed:                 0
% 0.76/0.87  sim_fw_subsumed:                        0
% 0.76/0.87  sim_bw_subsumed:                        0
% 0.76/0.87  sim_fw_subsumption_res:                 0
% 0.76/0.87  sim_bw_subsumption_res:                 0
% 0.76/0.87  sim_tautology_del:                      0
% 0.76/0.87  sim_eq_tautology_del:                   0
% 0.76/0.87  sim_eq_res_simp:                        0
% 0.76/0.87  sim_fw_demodulated:                     0
% 0.76/0.87  sim_bw_demodulated:                     0
% 0.76/0.87  sim_light_normalised:                   3
% 0.76/0.87  sim_joinable_taut:                      0
% 0.76/0.87  sim_joinable_simp:                      0
% 0.76/0.87  sim_ac_normalised:                      0
% 0.76/0.87  sim_smt_subsumption:                    0
% 0.76/0.87  
%------------------------------------------------------------------------------
