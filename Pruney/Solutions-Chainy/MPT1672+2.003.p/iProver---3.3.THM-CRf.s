%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:08 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :  261 (1694 expanded)
%              Number of clauses        :  185 ( 419 expanded)
%              Number of leaves         :   23 ( 444 expanded)
%              Depth                    :   27
%              Number of atoms          : 1300 (26404 expanded)
%              Number of equality atoms :  273 (3567 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X3,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | r2_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(X0,X6) = X5
                      & r1_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r1_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f47,plain,(
    ! [X0,X1,X5] :
      ( ? [X6] :
          ( k1_yellow_0(X0,X6) = X5
          & r1_yellow_0(X0,X6)
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
     => ( k1_yellow_0(X0,sK6(X5)) = X5
        & r1_yellow_0(X0,sK6(X5))
        & m1_subset_1(sK6(X5),k1_zfmisc_1(X1))
        & v1_finset_1(sK6(X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK5)
          | ~ r2_lattice3(X0,X1,sK5) )
        & ( r2_lattice3(X0,X2,sK5)
          | r2_lattice3(X0,X1,sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & ! [X4] :
              ( r2_hidden(k1_yellow_0(X0,X4),X2)
              | k1_xboole_0 = X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X4) )
          & ! [X5] :
              ( ? [X6] :
                  ( k1_yellow_0(X0,X6) = X5
                  & r1_yellow_0(X0,X6)
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & ! [X7] :
              ( r1_yellow_0(X0,X7)
              | k1_xboole_0 = X7
              | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X7) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ r2_lattice3(X0,sK4,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r2_lattice3(X0,sK4,X3)
              | r2_lattice3(X0,X1,X3) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & ! [X4] :
            ( r2_hidden(k1_yellow_0(X0,X4),sK4)
            | k1_xboole_0 = X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        & ! [X5] :
            ( ? [X6] :
                ( k1_yellow_0(X0,X6) = X5
                & r1_yellow_0(X0,X6)
                & m1_subset_1(X6,k1_zfmisc_1(X1))
                & v1_finset_1(X6) )
            | ~ r2_hidden(X5,sK4)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & ! [X7] :
            ( r1_yellow_0(X0,X7)
            | k1_xboole_0 = X7
            | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X7) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | r2_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(X0,X6) = X5
                      & r1_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r1_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,sK3,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | r2_lattice3(X0,sK3,X3) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & ! [X4] :
                ( r2_hidden(k1_yellow_0(X0,X4),X2)
                | k1_xboole_0 = X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
                | ~ v1_finset_1(X4) )
            & ! [X5] :
                ( ? [X6] :
                    ( k1_yellow_0(X0,X6) = X5
                    & r1_yellow_0(X0,X6)
                    & m1_subset_1(X6,k1_zfmisc_1(sK3))
                    & v1_finset_1(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & ! [X7] :
                ( r1_yellow_0(X0,X7)
                | k1_xboole_0 = X7
                | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
                | ~ v1_finset_1(X7) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | r2_lattice3(X0,X1,X3) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X4] :
                    ( r2_hidden(k1_yellow_0(X0,X4),X2)
                    | k1_xboole_0 = X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X4) )
                & ! [X5] :
                    ( ? [X6] :
                        ( k1_yellow_0(X0,X6) = X5
                        & r1_yellow_0(X0,X6)
                        & m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & ! [X7] :
                    ( r1_yellow_0(X0,X7)
                    | k1_xboole_0 = X7
                    | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X7) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK2,X2,X3)
                    | ~ r2_lattice3(sK2,X1,X3) )
                  & ( r2_lattice3(sK2,X2,X3)
                    | r2_lattice3(sK2,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(sK2,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(sK2,X6) = X5
                      & r1_yellow_0(sK2,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
              & ! [X7] :
                  ( r1_yellow_0(sK2,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r2_lattice3(sK2,sK4,sK5)
      | ~ r2_lattice3(sK2,sK3,sK5) )
    & ( r2_lattice3(sK2,sK4,sK5)
      | r2_lattice3(sK2,sK3,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & ! [X4] :
        ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X4) )
    & ! [X5] :
        ( ( k1_yellow_0(sK2,sK6(X5)) = X5
          & r1_yellow_0(sK2,sK6(X5))
          & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
          & v1_finset_1(sK6(X5)) )
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & ! [X7] :
        ( r1_yellow_0(sK2,X7)
        | k1_xboole_0 = X7
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).

fof(f72,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_476,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_2949,plain,
    ( k1_tarski(X0_52) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_38190,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2949])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X1)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_555,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X1)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_556,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_lattice3(sK2,X2,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_34])).

cnf(c_559,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_2947,plain,
    ( ~ r1_orders_2(sK2,X0_52,X1_52)
    | ~ r2_lattice3(sK2,X2_52,X0_52)
    | r2_lattice3(sK2,X2_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_559])).

cnf(c_4641,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
    | ~ r2_lattice3(sK2,X1_52,k1_yellow_0(sK2,X0_52))
    | r2_lattice3(sK2,X1_52,sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_10795,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(X1_52),k1_yellow_0(sK2,X0_52))
    | r2_lattice3(sK2,k1_tarski(X1_52),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4641])).

cnf(c_17889,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,X0_52))
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10795])).

cnf(c_34366,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_17889])).

cnf(c_34367,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34366])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_916,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_34])).

cnf(c_917,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_2928,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0_52,X1_52),X1_52)
    | r2_lattice3(sK2,X0_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_917])).

cnf(c_4714,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0_52,sK5),sK5)
    | r2_lattice3(sK2,X0_52,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_25528,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4714])).

cnf(c_25529,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25528])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_865,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_866,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_2931,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r2_lattice3(sK2,X2_52,X1_52)
    | ~ r2_hidden(X0_52,X2_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_866])).

cnf(c_11615,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),X0_52)
    | ~ r2_lattice3(sK2,sK4,X0_52)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_25175,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_11615])).

cnf(c_25176,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25175])).

cnf(c_2960,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_5532,plain,
    ( k1_tarski(sK0(sK2,X0_52,sK5)) = k1_tarski(sK0(sK2,X0_52,sK5)) ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_16719,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_5532])).

cnf(c_2961,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_5495,plain,
    ( X0_52 != X1_52
    | X0_52 = k1_xboole_0
    | k1_xboole_0 != X1_52 ),
    inference(instantiation,[status(thm)],[c_2961])).

cnf(c_7674,plain,
    ( X0_52 != k1_tarski(sK0(sK2,sK3,sK5))
    | X0_52 = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_5495])).

cnf(c_16718,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_7674])).

cnf(c_2966,plain,
    ( ~ r1_orders_2(X0_51,X0_52,X1_52)
    | r1_orders_2(X0_51,X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_5004,plain,
    ( ~ r1_orders_2(X0_51,X0_52,X1_52)
    | r1_orders_2(X0_51,X2_52,X1_52)
    | X2_52 != X0_52 ),
    inference(resolution,[status(thm)],[c_2966,c_2960])).

cnf(c_2962,plain,
    ( X0_52 != X1_52
    | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
    theory(equality)).

cnf(c_6326,plain,
    ( ~ r1_orders_2(X0_51,k1_zfmisc_1(X0_52),X1_52)
    | r1_orders_2(X0_51,k1_zfmisc_1(X2_52),X1_52)
    | X2_52 != X0_52 ),
    inference(resolution,[status(thm)],[c_5004,c_2962])).

cnf(c_24,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2956,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5175,plain,
    ( r1_orders_2(sK2,X0_52,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r2_hidden(X0_52,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_2931,c_2956])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5217,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ r2_hidden(X0_52,sK3)
    | r2_lattice3(sK2,sK4,sK5)
    | r1_orders_2(sK2,X0_52,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5175,c_25])).

cnf(c_5218,plain,
    ( r1_orders_2(sK2,X0_52,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r2_hidden(X0_52,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_5217])).

cnf(c_10669,plain,
    ( r1_orders_2(sK2,k1_zfmisc_1(X0_52),sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r2_hidden(k1_zfmisc_1(X1_52),sK3)
    | ~ m1_subset_1(k1_zfmisc_1(X1_52),u1_struct_0(sK2))
    | X0_52 != X1_52 ),
    inference(resolution,[status(thm)],[c_6326,c_5218])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_886,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_887,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_2930,plain,
    ( r2_lattice3(sK2,X0_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_887])).

cnf(c_3859,plain,
    ( r2_lattice3(sK2,X0_52,sK5)
    | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2930])).

cnf(c_3861,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_901,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_902,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_2929,plain,
    ( r2_lattice3(sK2,X0_52,X1_52)
    | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_902])).

cnf(c_3869,plain,
    ( r2_lattice3(sK2,X0_52,sK5)
    | r2_hidden(sK0(sK2,X0_52,sK5),X0_52)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_3871,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_4020,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2952,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0_52),k1_zfmisc_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_4198,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_28,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2953,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0_52))
    | ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4197,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_501,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_502,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_659,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_502,c_34])).

cnf(c_660,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_2943,plain,
    ( ~ r2_lattice3(sK2,X0_52,X1_52)
    | r2_lattice3(sK2,X2_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_660])).

cnf(c_3901,plain,
    ( r2_lattice3(sK2,X0_52,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_4580,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3901])).

cnf(c_4716,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4714])).

cnf(c_2955,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3733,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2955])).

cnf(c_3758,plain,
    ( r2_lattice3(sK2,X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2929])).

cnf(c_3757,plain,
    ( r2_lattice3(sK2,X0_52,X1_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2930])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2954,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3734,plain,
    ( k1_yellow_0(sK2,sK6(X0_52)) = X0_52
    | r2_hidden(X0_52,sK4) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2954])).

cnf(c_4890,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_52,X1_52))) = sK0(sK2,X0_52,X1_52)
    | r2_lattice3(sK2,X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,X1_52),sK4) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3757,c_3734])).

cnf(c_5060,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_52))) = sK0(sK2,sK4,X0_52)
    | r2_lattice3(sK2,sK4,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_4890])).

cnf(c_5433,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_5060])).

cnf(c_5436,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5433])).

cnf(c_5525,plain,
    ( sK0(sK2,X0_52,sK5) = sK0(sK2,X0_52,sK5) ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_5528,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5525])).

cnf(c_12,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_223,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_691,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_223,c_34])).

cnf(c_692,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_2941,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),X1_52)
    | ~ r2_lattice3(sK2,X0_52,X1_52)
    | ~ r1_yellow_0(sK2,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_692])).

cnf(c_4514,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0_52)
    | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0_52)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_6070,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4514])).

cnf(c_4473,plain,
    ( X0_52 != X1_52
    | X0_52 = k1_yellow_0(sK2,X2_52)
    | k1_yellow_0(sK2,X2_52) != X1_52 ),
    inference(instantiation,[status(thm)],[c_2961])).

cnf(c_5759,plain,
    ( X0_52 != sK0(sK2,sK4,sK5)
    | X0_52 = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4473])).

cnf(c_7373,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5759])).

cnf(c_4661,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,X2_52),sK5)
    | X0_52 != k1_yellow_0(sK2,X2_52)
    | X1_52 != sK5 ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_7125,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X0_52 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | X1_52 != sK5 ),
    inference(instantiation,[status(thm)],[c_4661])).

cnf(c_8029,plain,
    ( r1_orders_2(sK2,X0_52,sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X0_52 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7125])).

cnf(c_11694,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8029])).

cnf(c_11937,plain,
    ( r2_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10669,c_25,c_24,c_3861,c_3871,c_4020,c_4198,c_4197,c_4580,c_4716,c_5436,c_5528,c_6070,c_7373,c_11694])).

cnf(c_11939,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11937])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2958,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3730,plain,
    ( r2_hidden(X0_52,X1_52) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2958])).

cnf(c_4,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_605,plain,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_606,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_2945,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_52)),sK4)
    | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_52) ),
    inference(subtyping,[status(esa)],[c_606])).

cnf(c_3742,plain,
    ( k1_xboole_0 = k1_tarski(X0_52)
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_52)),sK4) = iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2945])).

cnf(c_793,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_794,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_2935,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_794])).

cnf(c_3752,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_4224,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,X0_52))) = k1_yellow_0(sK2,X0_52)
    | r2_hidden(k1_yellow_0(sK2,X0_52),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_3734])).

cnf(c_4677,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
    | k1_tarski(X0_52) = k1_xboole_0
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3742,c_4224])).

cnf(c_5338,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4677,c_2949])).

cnf(c_5344,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_5338])).

cnf(c_5428,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52)))
    | r2_lattice3(sK2,sK3,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_5344])).

cnf(c_6586,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_5428])).

cnf(c_3756,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
    | r2_lattice3(sK2,X2_52,X1_52) != iProver_top
    | r2_hidden(X0_52,X2_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2931])).

cnf(c_7414,plain,
    ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
    | r2_lattice3(sK2,X1_52,X0_52) != iProver_top
    | r2_hidden(sK5,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3756])).

cnf(c_7429,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top
    | r2_lattice3(sK2,X0_52,sK5) != iProver_top
    | r2_hidden(sK5,X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_7414])).

cnf(c_7598,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,sK5,sK5) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6586,c_7429])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_775,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_776,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_2936,plain,
    ( ~ r1_orders_2(sK2,X0_52,X1_52)
    | r2_lattice3(sK2,k1_tarski(X0_52),X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_776])).

cnf(c_3751,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
    | r2_lattice3(sK2,k1_tarski(X0_52),X1_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2936])).

cnf(c_3744,plain,
    ( r2_lattice3(sK2,X0_52,X1_52) != iProver_top
    | r2_lattice3(sK2,X2_52,X1_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2943])).

cnf(c_5125,plain,
    ( r2_lattice3(sK2,X0_52,sK5) != iProver_top
    | r2_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3744])).

cnf(c_6097,plain,
    ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
    | r2_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_5125])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8431,plain,
    ( m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | r2_lattice3(sK2,X1_52,sK5) = iProver_top
    | r1_orders_2(sK2,X0_52,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6097,c_58])).

cnf(c_8432,plain,
    ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
    | r2_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8431])).

cnf(c_8437,plain,
    ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
    | r2_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
    | r2_hidden(X1_52,k1_tarski(X0_52)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_8432])).

cnf(c_8443,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r2_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
    | r2_hidden(X0_52,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7598,c_8437])).

cnf(c_23,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2957,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3731,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2957])).

cnf(c_6693,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6586,c_3731])).

cnf(c_6695,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6693])).

cnf(c_11698,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8443,c_25,c_24,c_3861,c_3871,c_4020,c_4198,c_4197,c_4580,c_4716,c_5436,c_5528,c_6070,c_6695,c_7373,c_11694])).

cnf(c_11709,plain,
    ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11698,c_3752])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_215,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_216,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_709,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_216,c_34])).

cnf(c_710,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0))
    | ~ r1_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_2940,plain,
    ( r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X0_52))
    | ~ r1_yellow_0(sK2,X0_52) ),
    inference(subtyping,[status(esa)],[c_710])).

cnf(c_11595,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_11596,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11595])).

cnf(c_18,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_757,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_758,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_2937,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r2_lattice3(sK2,k1_tarski(X0_52),X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_4000,plain,
    ( r1_orders_2(sK2,X0_52,sK5)
    | ~ r2_lattice3(sK2,k1_tarski(X0_52),sK5)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_4271,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_52,sK5),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4000])).

cnf(c_7821,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4271])).

cnf(c_7822,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7821])).

cnf(c_31,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_590,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_591,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_2946,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0_52))
    | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_52) ),
    inference(subtyping,[status(esa)],[c_591])).

cnf(c_4973,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_4977,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4973])).

cnf(c_4974,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_4975,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4974])).

cnf(c_4964,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_4965,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4964])).

cnf(c_4112,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2958])).

cnf(c_4113,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4112])).

cnf(c_4014,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_4015,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4014])).

cnf(c_60,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38190,c_34367,c_25529,c_25176,c_16719,c_16718,c_11939,c_11709,c_11596,c_7822,c_4977,c_4975,c_4965,c_4113,c_4015,c_60,c_58])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:51:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.47/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.47/2.51  
% 15.47/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.51  
% 15.47/2.51  ------  iProver source info
% 15.47/2.51  
% 15.47/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.51  git: non_committed_changes: false
% 15.47/2.51  git: last_make_outside_of_git: false
% 15.47/2.51  
% 15.47/2.51  ------ 
% 15.47/2.51  ------ Parsing...
% 15.47/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.51  
% 15.47/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 15.47/2.51  
% 15.47/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.51  
% 15.47/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.51  ------ Proving...
% 15.47/2.51  ------ Problem Properties 
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  clauses                                 31
% 15.47/2.51  conjectures                             8
% 15.47/2.51  EPR                                     2
% 15.47/2.51  Horn                                    23
% 15.47/2.51  unary                                   5
% 15.47/2.51  binary                                  4
% 15.47/2.51  lits                                    99
% 15.47/2.51  lits eq                                 8
% 15.47/2.51  fd_pure                                 0
% 15.47/2.51  fd_pseudo                               0
% 15.47/2.51  fd_cond                                 0
% 15.47/2.51  fd_pseudo_cond                          3
% 15.47/2.51  AC symbols                              0
% 15.47/2.51  
% 15.47/2.51  ------ Input Options Time Limit: Unbounded
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  ------ 
% 15.47/2.51  Current options:
% 15.47/2.51  ------ 
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  ------ Proving...
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  % SZS status Theorem for theBenchmark.p
% 15.47/2.51  
% 15.47/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.51  
% 15.47/2.51  fof(f1,axiom,(
% 15.47/2.51    v1_xboole_0(k1_xboole_0)),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f49,plain,(
% 15.47/2.51    v1_xboole_0(k1_xboole_0)),
% 15.47/2.51    inference(cnf_transformation,[],[f1])).
% 15.47/2.51  
% 15.47/2.51  fof(f2,axiom,(
% 15.47/2.51    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f50,plain,(
% 15.47/2.51    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f2])).
% 15.47/2.51  
% 15.47/2.51  fof(f9,axiom,(
% 15.47/2.51    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f25,plain,(
% 15.47/2.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 15.47/2.51    inference(ennf_transformation,[],[f9])).
% 15.47/2.51  
% 15.47/2.51  fof(f26,plain,(
% 15.47/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f25])).
% 15.47/2.51  
% 15.47/2.51  fof(f65,plain,(
% 15.47/2.51    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f26])).
% 15.47/2.51  
% 15.47/2.51  fof(f12,conjecture,(
% 15.47/2.51    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f13,negated_conjecture,(
% 15.47/2.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 15.47/2.51    inference(negated_conjecture,[],[f12])).
% 15.47/2.51  
% 15.47/2.51  fof(f14,plain,(
% 15.47/2.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 15.47/2.51    inference(rectify,[],[f13])).
% 15.47/2.51  
% 15.47/2.51  fof(f16,plain,(
% 15.47/2.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 15.47/2.51    inference(pure_predicate_removal,[],[f14])).
% 15.47/2.51  
% 15.47/2.51  fof(f17,plain,(
% 15.47/2.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 15.47/2.51    inference(pure_predicate_removal,[],[f16])).
% 15.47/2.51  
% 15.47/2.51  fof(f29,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 15.47/2.51    inference(ennf_transformation,[],[f17])).
% 15.47/2.51  
% 15.47/2.51  fof(f30,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f29])).
% 15.47/2.51  
% 15.47/2.51  fof(f40,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 15.47/2.51    inference(nnf_transformation,[],[f30])).
% 15.47/2.51  
% 15.47/2.51  fof(f41,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f40])).
% 15.47/2.51  
% 15.47/2.51  fof(f42,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 15.47/2.51    inference(rectify,[],[f41])).
% 15.47/2.51  
% 15.47/2.51  fof(f47,plain,(
% 15.47/2.51    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f46,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f45,plain,(
% 15.47/2.51    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f44,plain,(
% 15.47/2.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f43,plain,(
% 15.47/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f48,plain,(
% 15.47/2.51    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 15.47/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).
% 15.47/2.51  
% 15.47/2.51  fof(f72,plain,(
% 15.47/2.51    v4_orders_2(sK2)),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f73,plain,(
% 15.47/2.51    l1_orders_2(sK2)),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f6,axiom,(
% 15.47/2.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f20,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(ennf_transformation,[],[f6])).
% 15.47/2.51  
% 15.47/2.51  fof(f21,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f20])).
% 15.47/2.51  
% 15.47/2.51  fof(f31,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(nnf_transformation,[],[f21])).
% 15.47/2.51  
% 15.47/2.51  fof(f32,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(rectify,[],[f31])).
% 15.47/2.51  
% 15.47/2.51  fof(f33,plain,(
% 15.47/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f34,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 15.47/2.51  
% 15.47/2.51  fof(f57,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f34])).
% 15.47/2.51  
% 15.47/2.51  fof(f54,plain,(
% 15.47/2.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f34])).
% 15.47/2.51  
% 15.47/2.51  fof(f83,plain,(
% 15.47/2.51    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f82,plain,(
% 15.47/2.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f55,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f34])).
% 15.47/2.51  
% 15.47/2.51  fof(f56,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f34])).
% 15.47/2.51  
% 15.47/2.51  fof(f78,plain,(
% 15.47/2.51    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f79,plain,(
% 15.47/2.51    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f4,axiom,(
% 15.47/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f15,plain,(
% 15.47/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 15.47/2.51    inference(unused_predicate_definition_removal,[],[f4])).
% 15.47/2.51  
% 15.47/2.51  fof(f19,plain,(
% 15.47/2.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 15.47/2.51    inference(ennf_transformation,[],[f15])).
% 15.47/2.51  
% 15.47/2.51  fof(f52,plain,(
% 15.47/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f19])).
% 15.47/2.51  
% 15.47/2.51  fof(f11,axiom,(
% 15.47/2.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f28,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(ennf_transformation,[],[f11])).
% 15.47/2.51  
% 15.47/2.51  fof(f71,plain,(
% 15.47/2.51    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f28])).
% 15.47/2.51  
% 15.47/2.51  fof(f80,plain,(
% 15.47/2.51    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f7,axiom,(
% 15.47/2.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f22,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(ennf_transformation,[],[f7])).
% 15.47/2.51  
% 15.47/2.51  fof(f23,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f22])).
% 15.47/2.51  
% 15.47/2.51  fof(f35,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(nnf_transformation,[],[f23])).
% 15.47/2.51  
% 15.47/2.51  fof(f36,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(flattening,[],[f35])).
% 15.47/2.51  
% 15.47/2.51  fof(f37,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(rectify,[],[f36])).
% 15.47/2.51  
% 15.47/2.51  fof(f38,plain,(
% 15.47/2.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 15.47/2.51    introduced(choice_axiom,[])).
% 15.47/2.51  
% 15.47/2.51  fof(f39,plain,(
% 15.47/2.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 15.47/2.51  
% 15.47/2.51  fof(f59,plain,(
% 15.47/2.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f39])).
% 15.47/2.51  
% 15.47/2.51  fof(f85,plain,(
% 15.47/2.51    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(equality_resolution,[],[f59])).
% 15.47/2.51  
% 15.47/2.51  fof(f8,axiom,(
% 15.47/2.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f24,plain,(
% 15.47/2.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(ennf_transformation,[],[f8])).
% 15.47/2.51  
% 15.47/2.51  fof(f63,plain,(
% 15.47/2.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f24])).
% 15.47/2.51  
% 15.47/2.51  fof(f3,axiom,(
% 15.47/2.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f18,plain,(
% 15.47/2.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 15.47/2.51    inference(ennf_transformation,[],[f3])).
% 15.47/2.51  
% 15.47/2.51  fof(f51,plain,(
% 15.47/2.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f18])).
% 15.47/2.51  
% 15.47/2.51  fof(f5,axiom,(
% 15.47/2.51    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f53,plain,(
% 15.47/2.51    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 15.47/2.51    inference(cnf_transformation,[],[f5])).
% 15.47/2.51  
% 15.47/2.51  fof(f81,plain,(
% 15.47/2.51    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f10,axiom,(
% 15.47/2.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 15.47/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.51  
% 15.47/2.51  fof(f27,plain,(
% 15.47/2.51    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.47/2.51    inference(ennf_transformation,[],[f10])).
% 15.47/2.51  
% 15.47/2.51  fof(f69,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f27])).
% 15.47/2.51  
% 15.47/2.51  fof(f84,plain,(
% 15.47/2.51    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  fof(f58,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f39])).
% 15.47/2.51  
% 15.47/2.51  fof(f86,plain,(
% 15.47/2.51    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(equality_resolution,[],[f58])).
% 15.47/2.51  
% 15.47/2.51  fof(f68,plain,(
% 15.47/2.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f27])).
% 15.47/2.51  
% 15.47/2.51  fof(f76,plain,(
% 15.47/2.51    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 15.47/2.51    inference(cnf_transformation,[],[f48])).
% 15.47/2.51  
% 15.47/2.51  cnf(c_0,plain,
% 15.47/2.51      ( v1_xboole_0(k1_xboole_0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_1,plain,
% 15.47/2.51      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_476,plain,
% 15.47/2.51      ( k1_tarski(X0) != k1_xboole_0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2949,plain,
% 15.47/2.51      ( k1_tarski(X0_52) != k1_xboole_0 ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_476]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_38190,plain,
% 15.47/2.51      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2949]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_15,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X3,X1)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | ~ v4_orders_2(X0)
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f65]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_35,negated_conjecture,
% 15.47/2.51      ( v4_orders_2(sK2) ),
% 15.47/2.51      inference(cnf_transformation,[],[f72]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_555,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X3,X1)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0)
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_556,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,X0,X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2,X0)
% 15.47/2.51      | r2_lattice3(sK2,X2,X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.47/2.51      | ~ l1_orders_2(sK2) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_555]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_34,negated_conjecture,
% 15.47/2.51      ( l1_orders_2(sK2) ),
% 15.47/2.51      inference(cnf_transformation,[],[f73]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_558,plain,
% 15.47/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | r2_lattice3(sK2,X2,X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2,X0)
% 15.47/2.51      | ~ r1_orders_2(sK2,X0,X1) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_556,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_559,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,X0,X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2,X0)
% 15.47/2.51      | r2_lattice3(sK2,X2,X1)
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(renaming,[status(thm)],[c_558]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2947,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2_52,X0_52)
% 15.47/2.51      | r2_lattice3(sK2,X2_52,X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_559]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4641,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,X1_52,k1_yellow_0(sK2,X0_52))
% 15.47/2.51      | r2_lattice3(sK2,X1_52,sK5)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2947]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_10795,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(X1_52),k1_yellow_0(sK2,X0_52))
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X1_52),sK5)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4641]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_17889,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,X0_52))
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_10795]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_34366,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_17889]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_34367,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_34366]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 15.47/2.51      | r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_916,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 15.47/2.51      | r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_5,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_917,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 15.47/2.51      | r2_lattice3(sK2,X0,X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_916]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2928,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,sK0(sK2,X0_52,X1_52),X1_52)
% 15.47/2.51      | r2_lattice3(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_917]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4714,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,sK0(sK2,X0_52,sK5),sK5)
% 15.47/2.51      | r2_lattice3(sK2,X0_52,sK5)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2928]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_25528,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK3,sK5)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4714]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_25529,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_25528]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8,plain,
% 15.47/2.51      ( r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ r2_hidden(X1,X3)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_865,plain,
% 15.47/2.51      ( r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ r2_hidden(X1,X3)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_866,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0,X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2,X1)
% 15.47/2.51      | ~ r2_hidden(X0,X2)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_865]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2931,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,X2_52,X1_52)
% 15.47/2.51      | ~ r2_hidden(X0_52,X2_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_866]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11615,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),X0_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK4,X0_52)
% 15.47/2.51      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2931]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_25175,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_11615]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_25176,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5) != iProver_top
% 15.47/2.51      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top
% 15.47/2.51      | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_25175]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2960,plain,( X0_52 = X0_52 ),theory(equality) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5532,plain,
% 15.47/2.51      ( k1_tarski(sK0(sK2,X0_52,sK5)) = k1_tarski(sK0(sK2,X0_52,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2960]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_16719,plain,
% 15.47/2.51      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_5532]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2961,plain,
% 15.47/2.51      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 15.47/2.51      theory(equality) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5495,plain,
% 15.47/2.51      ( X0_52 != X1_52 | X0_52 = k1_xboole_0 | k1_xboole_0 != X1_52 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2961]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7674,plain,
% 15.47/2.51      ( X0_52 != k1_tarski(sK0(sK2,sK3,sK5))
% 15.47/2.51      | X0_52 = k1_xboole_0
% 15.47/2.51      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_5495]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_16718,plain,
% 15.47/2.51      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 15.47/2.51      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 15.47/2.51      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_7674]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2966,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0_51,X0_52,X1_52)
% 15.47/2.51      | r1_orders_2(X0_51,X2_52,X3_52)
% 15.47/2.51      | X2_52 != X0_52
% 15.47/2.51      | X3_52 != X1_52 ),
% 15.47/2.51      theory(equality) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5004,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0_51,X0_52,X1_52)
% 15.47/2.51      | r1_orders_2(X0_51,X2_52,X1_52)
% 15.47/2.51      | X2_52 != X0_52 ),
% 15.47/2.51      inference(resolution,[status(thm)],[c_2966,c_2960]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2962,plain,
% 15.47/2.51      ( X0_52 != X1_52 | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
% 15.47/2.51      theory(equality) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6326,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0_51,k1_zfmisc_1(X0_52),X1_52)
% 15.47/2.51      | r1_orders_2(X0_51,k1_zfmisc_1(X2_52),X1_52)
% 15.47/2.51      | X2_52 != X0_52 ),
% 15.47/2.51      inference(resolution,[status(thm)],[c_5004,c_2962]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_24,negated_conjecture,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 15.47/2.51      inference(cnf_transformation,[],[f83]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2956,negated_conjecture,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_24]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5175,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | ~ r2_hidden(X0_52,sK3)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(resolution,[status(thm)],[c_2931,c_2956]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_25,negated_conjecture,
% 15.47/2.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f82]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5217,plain,
% 15.47/2.51      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ r2_hidden(X0_52,sK3)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | r1_orders_2(sK2,X0_52,sK5) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_5175,c_25]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5218,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | ~ r2_hidden(X0_52,sK3)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(renaming,[status(thm)],[c_5217]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_10669,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_zfmisc_1(X0_52),sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | ~ r2_hidden(k1_zfmisc_1(X1_52),sK3)
% 15.47/2.51      | ~ m1_subset_1(k1_zfmisc_1(X1_52),u1_struct_0(sK2))
% 15.47/2.51      | X0_52 != X1_52 ),
% 15.47/2.51      inference(resolution,[status(thm)],[c_6326,c_5218]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_886,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_887,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0,X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_886]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2930,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_887]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3859,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,sK5)
% 15.47/2.51      | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2930]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3861,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_3859]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_hidden(sK0(X0,X1,X2),X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_901,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_hidden(sK0(X0,X1,X2),X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_902,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0,X1)
% 15.47/2.51      | r2_hidden(sK0(sK2,X0,X1),X0)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_901]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2929,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,X1_52)
% 15.47/2.51      | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_902]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3869,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,sK5)
% 15.47/2.51      | r2_hidden(sK0(sK2,X0_52,sK5),X0_52)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2929]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3871,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_3869]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4020,plain,
% 15.47/2.51      ( sK5 = sK5 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2960]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_29,negated_conjecture,
% 15.47/2.51      ( ~ r2_hidden(X0,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.47/2.51      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f78]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2952,negated_conjecture,
% 15.47/2.51      ( ~ r2_hidden(X0_52,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | m1_subset_1(sK6(X0_52),k1_zfmisc_1(sK3)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_29]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4198,plain,
% 15.47/2.51      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 15.47/2.51      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 15.47/2.51      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2952]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_28,negated_conjecture,
% 15.47/2.51      ( r1_yellow_0(sK2,sK6(X0))
% 15.47/2.51      | ~ r2_hidden(X0,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f79]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2953,negated_conjecture,
% 15.47/2.51      ( r1_yellow_0(sK2,sK6(X0_52))
% 15.47/2.51      | ~ r2_hidden(X0_52,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_28]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4197,plain,
% 15.47/2.51      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 15.47/2.51      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2953]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3,plain,
% 15.47/2.51      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_21,plain,
% 15.47/2.51      ( ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ r1_tarski(X3,X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f71]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_501,plain,
% 15.47/2.51      ( ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.47/2.51      | ~ l1_orders_2(X0)
% 15.47/2.51      | X3 != X4
% 15.47/2.51      | X1 != X5 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_502,plain,
% 15.47/2.51      ( ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_501]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_659,plain,
% 15.47/2.51      ( ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,X3,X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_502,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_660,plain,
% 15.47/2.51      ( ~ r2_lattice3(sK2,X0,X1)
% 15.47/2.51      | r2_lattice3(sK2,X2,X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_659]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2943,plain,
% 15.47/2.51      ( ~ r2_lattice3(sK2,X0_52,X1_52)
% 15.47/2.51      | r2_lattice3(sK2,X2_52,X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_660]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3901,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK3,sK5)
% 15.47/2.51      | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK3))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2943]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4580,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK3,sK5)
% 15.47/2.51      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_3901]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4716,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4714]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2955,negated_conjecture,
% 15.47/2.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_25]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3733,plain,
% 15.47/2.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2955]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3758,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,X1_52) = iProver_top
% 15.47/2.51      | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2929]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3757,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,X1_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2930]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_27,negated_conjecture,
% 15.47/2.51      ( ~ r2_hidden(X0,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.47/2.51      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 15.47/2.51      inference(cnf_transformation,[],[f80]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2954,negated_conjecture,
% 15.47/2.51      ( ~ r2_hidden(X0_52,sK4)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | k1_yellow_0(sK2,sK6(X0_52)) = X0_52 ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_27]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3734,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(X0_52)) = X0_52
% 15.47/2.51      | r2_hidden(X0_52,sK4) != iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2954]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4890,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_52,X1_52))) = sK0(sK2,X0_52,X1_52)
% 15.47/2.51      | r2_lattice3(sK2,X0_52,X1_52) = iProver_top
% 15.47/2.51      | r2_hidden(sK0(sK2,X0_52,X1_52),sK4) != iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3757,c_3734]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5060,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_52))) = sK0(sK2,sK4,X0_52)
% 15.47/2.51      | r2_lattice3(sK2,sK4,X0_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3758,c_4890]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5433,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3733,c_5060]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5436,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
% 15.47/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_5433]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5525,plain,
% 15.47/2.51      ( sK0(sK2,X0_52,sK5) = sK0(sK2,X0_52,sK5) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2960]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5528,plain,
% 15.47/2.51      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_5525]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_12,plain,
% 15.47/2.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f85]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_14,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_222,plain,
% 15.47/2.51      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_12,c_14]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_223,plain,
% 15.47/2.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(renaming,[status(thm)],[c_222]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_691,plain,
% 15.47/2.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.47/2.51      | ~ r2_lattice3(X0,X1,X2)
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_223,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_692,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,X0,X1)
% 15.47/2.51      | ~ r1_yellow_0(sK2,X0)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_691]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2941,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),X1_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r1_yellow_0(sK2,X0_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_692]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4514,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0_52)
% 15.47/2.51      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2941]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6070,plain,
% 15.47/2.51      ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 15.47/2.51      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4514]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4473,plain,
% 15.47/2.51      ( X0_52 != X1_52
% 15.47/2.51      | X0_52 = k1_yellow_0(sK2,X2_52)
% 15.47/2.51      | k1_yellow_0(sK2,X2_52) != X1_52 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2961]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5759,plain,
% 15.47/2.51      ( X0_52 != sK0(sK2,sK4,sK5)
% 15.47/2.51      | X0_52 = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4473]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7373,plain,
% 15.47/2.51      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 15.47/2.51      | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_5759]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4661,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,X2_52),sK5)
% 15.47/2.51      | X0_52 != k1_yellow_0(sK2,X2_52)
% 15.47/2.51      | X1_52 != sK5 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2966]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7125,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 15.47/2.51      | X0_52 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | X1_52 != sK5 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4661]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8029,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5)
% 15.47/2.51      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 15.47/2.51      | X0_52 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | sK5 != sK5 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_7125]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11694,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 15.47/2.51      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 15.47/2.51      | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 15.47/2.51      | sK5 != sK5 ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_8029]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11937,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK4,sK5) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_10669,c_25,c_24,c_3861,c_3871,c_4020,c_4198,c_4197,
% 15.47/2.51                 c_4580,c_4716,c_5436,c_5528,c_6070,c_7373,c_11694]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11939,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_11937]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2,plain,
% 15.47/2.51      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2958,plain,
% 15.47/2.51      ( ~ r2_hidden(X0_52,X1_52)
% 15.47/2.51      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_2]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3730,plain,
% 15.47/2.51      ( r2_hidden(X0_52,X1_52) != iProver_top
% 15.47/2.51      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2958]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4,plain,
% 15.47/2.51      ( v1_finset_1(k1_tarski(X0)) ),
% 15.47/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_26,negated_conjecture,
% 15.47/2.51      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 15.47/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 15.47/2.51      | ~ v1_finset_1(X0)
% 15.47/2.51      | k1_xboole_0 = X0 ),
% 15.47/2.51      inference(cnf_transformation,[],[f81]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_605,plain,
% 15.47/2.51      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 15.47/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_tarski(X1) != X0
% 15.47/2.51      | k1_xboole_0 = X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_606,plain,
% 15.47/2.51      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(X0) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_605]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2945,plain,
% 15.47/2.51      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_52)),sK4)
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(X0_52) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_606]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3742,plain,
% 15.47/2.51      ( k1_xboole_0 = k1_tarski(X0_52)
% 15.47/2.51      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_52)),sK4) = iProver_top
% 15.47/2.51      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2945]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_793,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_794,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_793]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2935,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_794]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3752,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2935]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4224,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,X0_52))) = k1_yellow_0(sK2,X0_52)
% 15.47/2.51      | r2_hidden(k1_yellow_0(sK2,X0_52),sK4) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3752,c_3734]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4677,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
% 15.47/2.51      | k1_tarski(X0_52) = k1_xboole_0
% 15.47/2.51      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3742,c_4224]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5338,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
% 15.47/2.51      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_4677,c_2949]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5344,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0_52)))) = k1_yellow_0(sK2,k1_tarski(X0_52))
% 15.47/2.51      | r2_hidden(X0_52,sK3) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3730,c_5338]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5428,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52)))
% 15.47/2.51      | r2_lattice3(sK2,sK3,X0_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3758,c_5344]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6586,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 15.47/2.51      | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3733,c_5428]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3756,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X2_52,X1_52) != iProver_top
% 15.47/2.51      | r2_hidden(X0_52,X2_52) != iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2931]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7414,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X1_52,X0_52) != iProver_top
% 15.47/2.51      | r2_hidden(sK5,X1_52) != iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3733,c_3756]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7429,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK5,sK5) = iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X0_52,sK5) != iProver_top
% 15.47/2.51      | r2_hidden(sK5,X0_52) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3733,c_7414]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7598,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 15.47/2.51      | r1_orders_2(sK2,sK5,sK5) = iProver_top
% 15.47/2.51      | r2_hidden(sK5,sK3) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_6586,c_7429]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_17,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,k1_tarski(X1),X2)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f69]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_775,plain,
% 15.47/2.51      ( ~ r1_orders_2(X0,X1,X2)
% 15.47/2.51      | r2_lattice3(X0,k1_tarski(X1),X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_776,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,X0,X1)
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X0),X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_775]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2936,plain,
% 15.47/2.51      ( ~ r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X0_52),X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_776]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3751,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X0_52),X1_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2936]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3744,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,X1_52) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X2_52,X1_52) = iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2943]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_5125,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X1_52,sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,k1_zfmisc_1(X0_52)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3733,c_3744]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6097,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X1_52,sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3751,c_5125]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_58,plain,
% 15.47/2.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8431,plain,
% 15.47/2.51      ( m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X1_52,sK5) = iProver_top
% 15.47/2.51      | r1_orders_2(sK2,X0_52,sK5) != iProver_top ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_6097,c_58]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8432,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,X1_52,sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top ),
% 15.47/2.51      inference(renaming,[status(thm)],[c_8431]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8437,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
% 15.47/2.51      | r2_hidden(X1_52,k1_tarski(X0_52)) != iProver_top
% 15.47/2.51      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_3730,c_8432]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_8443,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
% 15.47/2.51      | r2_hidden(X0_52,k1_tarski(sK5)) != iProver_top
% 15.47/2.51      | r2_hidden(sK5,sK3) != iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_7598,c_8437]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_23,negated_conjecture,
% 15.47/2.51      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 15.47/2.51      inference(cnf_transformation,[],[f84]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2957,negated_conjecture,
% 15.47/2.51      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_23]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_3731,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_2957]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6693,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_6586,c_3731]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_6695,plain,
% 15.47/2.51      ( ~ r2_lattice3(sK2,sK4,sK5)
% 15.47/2.51      | k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
% 15.47/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_6693]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11698,plain,
% 15.47/2.51      ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_8443,c_25,c_24,c_3861,c_3871,c_4020,c_4198,c_4197,
% 15.47/2.51                 c_4580,c_4716,c_5436,c_5528,c_6070,c_6695,c_7373,
% 15.47/2.51                 c_11694]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11709,plain,
% 15.47/2.51      ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top ),
% 15.47/2.51      inference(superposition,[status(thm)],[c_11698,c_3752]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_13,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f86]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_215,plain,
% 15.47/2.51      ( ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(global_propositional_subsumption,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_13,c_14]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_216,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(renaming,[status(thm)],[c_215]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_709,plain,
% 15.47/2.51      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 15.47/2.51      | ~ r1_yellow_0(X0,X1)
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_216,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_710,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) | ~ r1_yellow_0(sK2,X0) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_709]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2940,plain,
% 15.47/2.51      ( r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X0_52))
% 15.47/2.51      | ~ r1_yellow_0(sK2,X0_52) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_710]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11595,plain,
% 15.47/2.51      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 15.47/2.51      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2940]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_11596,plain,
% 15.47/2.51      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
% 15.47/2.51      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_11595]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_18,plain,
% 15.47/2.51      ( r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ l1_orders_2(X0) ),
% 15.47/2.51      inference(cnf_transformation,[],[f68]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_757,plain,
% 15.47/2.51      ( r1_orders_2(X0,X1,X2)
% 15.47/2.51      | ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 15.47/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.47/2.51      | sK2 != X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_758,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0,X1)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 15.47/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_757]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2937,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,X1_52)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(X0_52),X1_52)
% 15.47/2.51      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_758]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4000,plain,
% 15.47/2.51      ( r1_orders_2(sK2,X0_52,sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(X0_52),sK5)
% 15.47/2.51      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2937]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4271,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK0(sK2,X0_52,sK5),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5)
% 15.47/2.51      | ~ m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4000]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7821,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 15.47/2.51      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 15.47/2.51      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_4271]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_7822,plain,
% 15.47/2.51      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 15.47/2.51      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
% 15.47/2.51      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_7821]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_31,negated_conjecture,
% 15.47/2.51      ( r1_yellow_0(sK2,X0)
% 15.47/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 15.47/2.51      | ~ v1_finset_1(X0)
% 15.47/2.51      | k1_xboole_0 = X0 ),
% 15.47/2.51      inference(cnf_transformation,[],[f76]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_590,plain,
% 15.47/2.51      ( r1_yellow_0(sK2,X0)
% 15.47/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_tarski(X1) != X0
% 15.47/2.51      | k1_xboole_0 = X0 ),
% 15.47/2.51      inference(resolution_lifted,[status(thm)],[c_4,c_31]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_591,plain,
% 15.47/2.51      ( r1_yellow_0(sK2,k1_tarski(X0))
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(X0) ),
% 15.47/2.51      inference(unflattening,[status(thm)],[c_590]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_2946,plain,
% 15.47/2.51      ( r1_yellow_0(sK2,k1_tarski(X0_52))
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(X0_52) ),
% 15.47/2.51      inference(subtyping,[status(esa)],[c_591]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4973,plain,
% 15.47/2.51      ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2946]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4977,plain,
% 15.47/2.51      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 15.47/2.51      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 15.47/2.51      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_4973]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4974,plain,
% 15.47/2.51      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 15.47/2.51      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 15.47/2.51      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2945]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4975,plain,
% 15.47/2.51      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 15.47/2.51      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
% 15.47/2.51      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_4974]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4964,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5)
% 15.47/2.51      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_3859]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4965,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 15.47/2.51      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_4964]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4112,plain,
% 15.47/2.51      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 15.47/2.51      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_2958]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4113,plain,
% 15.47/2.51      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 15.47/2.51      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_4112]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4014,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5)
% 15.47/2.51      | r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 15.47/2.51      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 15.47/2.51      inference(instantiation,[status(thm)],[c_3869]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_4015,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 15.47/2.51      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
% 15.47/2.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_4014]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(c_60,plain,
% 15.47/2.51      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 15.47/2.51      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 15.47/2.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.47/2.51  
% 15.47/2.51  cnf(contradiction,plain,
% 15.47/2.51      ( $false ),
% 15.47/2.51      inference(minisat,
% 15.47/2.51                [status(thm)],
% 15.47/2.51                [c_38190,c_34367,c_25529,c_25176,c_16719,c_16718,c_11939,
% 15.47/2.51                 c_11709,c_11596,c_7822,c_4977,c_4975,c_4965,c_4113,
% 15.47/2.51                 c_4015,c_60,c_58]) ).
% 15.47/2.51  
% 15.47/2.51  
% 15.47/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.51  
% 15.47/2.51  ------                               Statistics
% 15.47/2.51  
% 15.47/2.51  ------ Selected
% 15.47/2.51  
% 15.47/2.51  total_time:                             1.82
% 15.47/2.51  
%------------------------------------------------------------------------------
