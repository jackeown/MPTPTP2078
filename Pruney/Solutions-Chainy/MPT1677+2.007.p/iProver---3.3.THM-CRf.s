%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:11 EST 2020

% Result     : Theorem 22.83s
% Output     : CNFRefutation 22.83s
% Verified   : 
% Statistics : Number of formulae       :  237 (1622 expanded)
%              Number of clauses        :  157 ( 371 expanded)
%              Number of leaves         :   24 ( 435 expanded)
%              Depth                    :   34
%              Number of atoms          : 1257 (25842 expanded)
%              Number of equality atoms :  334 (3706 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X3)
                      <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r1_lattice3(X0,X2,X7)
                    | ~ r1_lattice3(X0,X1,X7) )
                  & ( r1_lattice3(X0,X2,X7)
                    | r1_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r1_lattice3(X0,X2,X7)
                    | ~ r1_lattice3(X0,X1,X7) )
                  & ( r1_lattice3(X0,X2,X7)
                    | r1_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | r1_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k2_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k2_yellow_0(X0,X6) = X5
                      & r2_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r2_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f48,plain,(
    ! [X0,X1,X5] :
      ( ? [X6] :
          ( k2_yellow_0(X0,X6) = X5
          & r2_yellow_0(X0,X6)
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
     => ( k2_yellow_0(X0,sK6(X5)) = X5
        & r2_yellow_0(X0,sK6(X5))
        & m1_subset_1(sK6(X5),k1_zfmisc_1(X1))
        & v1_finset_1(sK6(X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK5)
          | ~ r1_lattice3(X0,X1,sK5) )
        & ( r1_lattice3(X0,X2,sK5)
          | r1_lattice3(X0,X1,sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & ! [X4] :
              ( r2_hidden(k2_yellow_0(X0,X4),X2)
              | k1_xboole_0 = X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X4) )
          & ! [X5] :
              ( ? [X6] :
                  ( k2_yellow_0(X0,X6) = X5
                  & r2_yellow_0(X0,X6)
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & ! [X7] :
              ( r2_yellow_0(X0,X7)
              | k1_xboole_0 = X7
              | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X7) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ r1_lattice3(X0,sK4,X3)
              | ~ r1_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,sK4,X3)
              | r1_lattice3(X0,X1,X3) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & ! [X4] :
            ( r2_hidden(k2_yellow_0(X0,X4),sK4)
            | k1_xboole_0 = X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        & ! [X5] :
            ( ? [X6] :
                ( k2_yellow_0(X0,X6) = X5
                & r2_yellow_0(X0,X6)
                & m1_subset_1(X6,k1_zfmisc_1(X1))
                & v1_finset_1(X6) )
            | ~ r2_hidden(X5,sK4)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & ! [X7] :
            ( r2_yellow_0(X0,X7)
            | k1_xboole_0 = X7
            | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X7) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | r1_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k2_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k2_yellow_0(X0,X6) = X5
                      & r2_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r2_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,sK3,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | r1_lattice3(X0,sK3,X3) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & ! [X4] :
                ( r2_hidden(k2_yellow_0(X0,X4),X2)
                | k1_xboole_0 = X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
                | ~ v1_finset_1(X4) )
            & ! [X5] :
                ( ? [X6] :
                    ( k2_yellow_0(X0,X6) = X5
                    & r2_yellow_0(X0,X6)
                    & m1_subset_1(X6,k1_zfmisc_1(sK3))
                    & v1_finset_1(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & ! [X7] :
                ( r2_yellow_0(X0,X7)
                | k1_xboole_0 = X7
                | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
                | ~ v1_finset_1(X7) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | r1_lattice3(X0,X1,X3) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X4] :
                    ( r2_hidden(k2_yellow_0(X0,X4),X2)
                    | k1_xboole_0 = X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X4) )
                & ! [X5] :
                    ( ? [X6] :
                        ( k2_yellow_0(X0,X6) = X5
                        & r2_yellow_0(X0,X6)
                        & m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & ! [X7] :
                    ( r2_yellow_0(X0,X7)
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
                  ( ( ~ r1_lattice3(sK2,X2,X3)
                    | ~ r1_lattice3(sK2,X1,X3) )
                  & ( r1_lattice3(sK2,X2,X3)
                    | r1_lattice3(sK2,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & ! [X4] :
                  ( r2_hidden(k2_yellow_0(sK2,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k2_yellow_0(sK2,X6) = X5
                      & r2_yellow_0(sK2,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
              & ! [X7] :
                  ( r2_yellow_0(sK2,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r1_lattice3(sK2,sK4,sK5)
      | ~ r1_lattice3(sK2,sK3,sK5) )
    & ( r1_lattice3(sK2,sK4,sK5)
      | r1_lattice3(sK2,sK3,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & ! [X4] :
        ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X4) )
    & ! [X5] :
        ( ( k2_yellow_0(sK2,sK6(X5)) = X5
          & r2_yellow_0(sK2,sK6(X5))
          & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
          & v1_finset_1(sK6(X5)) )
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & ! [X7] :
        ( r2_yellow_0(sK2,X7)
        | k1_xboole_0 = X7
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).

fof(f74,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f61])).

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

fof(f28,plain,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f53,plain,(
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

fof(f29,plain,(
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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X5] :
      ( r2_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X5] :
      ( k2_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X7] :
      ( r2_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_887,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_888,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_3691,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3719,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_594,plain,
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_595,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_3706,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3711,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3718,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4255,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_3718])).

cnf(c_14,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_752,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_753,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_3698,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_4718,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_3698])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3715,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_521,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_522,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,X2,X0)
    | ~ r1_lattice3(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_34])).

cnf(c_525,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_3709,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,X1) != iProver_top
    | r1_lattice3(sK2,X2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_6872,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3715,c_3709])).

cnf(c_6929,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_6872])).

cnf(c_10964,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
    | r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4718,c_6929])).

cnf(c_24,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3716,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_767,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_768,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
    | ~ r1_lattice3(sK2,X1,X0)
    | ~ r2_yellow_0(sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_3697,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1)) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r2_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_7441,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1)) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r2_yellow_0(sK2,X1) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_3697])).

cnf(c_17,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_734,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_735,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_3699,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r1_orders_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_490,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_491,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_648,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_491,c_34])).

cnf(c_649,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_3704,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_5241,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_3704])).

cnf(c_10511,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X2,X1) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_tarski(X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3699,c_5241])).

cnf(c_24686,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X2,X1) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_tarski(X2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10511,c_4255])).

cnf(c_24688,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r1_orders_2(sK2,X2,X1) != iProver_top
    | r2_hidden(X0,k1_tarski(X2)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3719,c_24686])).

cnf(c_26098,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),k2_yellow_0(sK2,X1)) = iProver_top
    | r1_lattice3(sK2,X1,X2) != iProver_top
    | r2_yellow_0(sK2,X1) != iProver_top
    | r2_hidden(X0,k1_tarski(X2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7441,c_24688])).

cnf(c_62683,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),k2_yellow_0(sK2,sK3)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_yellow_0(sK2,sK3) != iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,sK3),sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_26098])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_59,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2951,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2962,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2951])).

cnf(c_2943,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2968,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_872,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_873,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_4028,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_4163,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_4164,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4163])).

cnf(c_4033,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | r2_hidden(sK0(sK2,X0,sK5),X0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_4177,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4033])).

cnf(c_4178,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4177])).

cnf(c_4189,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_28,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4476,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4477,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4476])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4475,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4479,plain,
    ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4475])).

cnf(c_4637,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_22,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_471,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_472,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_664,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_34])).

cnf(c_665,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_4067,plain,
    ( ~ r1_lattice3(sK2,X0,sK5)
    | r1_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_4831,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4067])).

cnf(c_4832,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
    | r1_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4831])).

cnf(c_2946,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4437,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | X0 != sK0(sK2,sK4,sK5)
    | X1 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_4820,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
    | X0 != u1_struct_0(sK2)
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4437])).

cnf(c_5425,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4820])).

cnf(c_5426,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5425])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_902,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_903,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_5710,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_5711,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5710])).

cnf(c_4859,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_8952,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_8953,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) = iProver_top
    | r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
    | r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8952])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3714,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4386,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_3714])).

cnf(c_4884,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r1_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3691,c_4386])).

cnf(c_9655,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3715,c_4884])).

cnf(c_2944,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6022,plain,
    ( X0 != X1
    | sK0(sK2,sK4,sK5) != X1
    | sK0(sK2,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_2944])).

cnf(c_11182,plain,
    ( X0 != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = X0
    | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6022])).

cnf(c_23115,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_11182])).

cnf(c_2950,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_11583,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | X2 != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | X1 != sK5
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2950])).

cnf(c_16478,plain,
    ( r1_orders_2(X0,sK5,X1)
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | X1 != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | X0 != sK2
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_11583])).

cnf(c_61026,plain,
    ( r1_orders_2(X0,sK5,sK0(sK2,sK4,sK5))
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | X0 != sK2
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_16478])).

cnf(c_61027,plain,
    ( X0 != sK2
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | r1_orders_2(X0,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61026])).

cnf(c_61029,plain,
    ( sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61027])).

cnf(c_63772,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62683,c_58,c_59,c_2962,c_2968,c_4164,c_4178,c_4189,c_4477,c_4479,c_4637,c_4832,c_5426,c_5711,c_8953,c_9655,c_23115,c_61029])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_851,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_852,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_3693,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_6220,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,X1,sK5) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3715,c_3693])).

cnf(c_6406,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,X1,sK5) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_6220])).

cnf(c_63793,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_63772,c_6406])).

cnf(c_79059,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10964,c_63793])).

cnf(c_79063,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
    | r2_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_79059])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_465,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_4904,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2944,c_2943])).

cnf(c_31,negated_conjecture,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_579,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_580,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_7162,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_tarski(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4904,c_580])).

cnf(c_7642,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_yellow_0(sK2,k1_tarski(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7162,c_465])).

cnf(c_7643,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) ),
    inference(renaming,[status(thm)],[c_7642])).

cnf(c_7644,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7643])).

cnf(c_79869,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_79063,c_465,c_7644])).

cnf(c_79877,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3719,c_79869])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_680,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_681,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_3702,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X1),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_81695,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_79877,c_3702])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3710,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4256,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3710,c_3718])).

cnf(c_83212,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_81695,c_58,c_4256])).

cnf(c_3690,plain,
    ( r1_orders_2(sK2,X0,sK0(sK2,X1,X0)) != iProver_top
    | r1_lattice3(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_83231,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_83212,c_3690])).

cnf(c_83443,plain,
    ( r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
    | r1_lattice3(sK2,X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_83231,c_58])).

cnf(c_83444,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_83443])).

cnf(c_83451,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3691,c_83444])).

cnf(c_23,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83451,c_63772,c_60,c_58])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 22.83/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.83/3.50  
% 22.83/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.83/3.50  
% 22.83/3.50  ------  iProver source info
% 22.83/3.50  
% 22.83/3.50  git: date: 2020-06-30 10:37:57 +0100
% 22.83/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.83/3.50  git: non_committed_changes: false
% 22.83/3.50  git: last_make_outside_of_git: false
% 22.83/3.50  
% 22.83/3.50  ------ 
% 22.83/3.50  ------ Parsing...
% 22.83/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.83/3.50  
% 22.83/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 22.83/3.50  
% 22.83/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.83/3.50  
% 22.83/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.83/3.50  ------ Proving...
% 22.83/3.50  ------ Problem Properties 
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  clauses                                 31
% 22.83/3.50  conjectures                             8
% 22.83/3.50  EPR                                     2
% 22.83/3.50  Horn                                    23
% 22.83/3.50  unary                                   4
% 22.83/3.50  binary                                  3
% 22.83/3.50  lits                                    103
% 22.83/3.50  lits eq                                 8
% 22.83/3.50  fd_pure                                 0
% 22.83/3.50  fd_pseudo                               0
% 22.83/3.50  fd_cond                                 0
% 22.83/3.50  fd_pseudo_cond                          3
% 22.83/3.50  AC symbols                              0
% 22.83/3.50  
% 22.83/3.50  ------ Input Options Time Limit: Unbounded
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  ------ 
% 22.83/3.50  Current options:
% 22.83/3.50  ------ 
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  ------ Proving...
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  % SZS status Theorem for theBenchmark.p
% 22.83/3.50  
% 22.83/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 22.83/3.50  
% 22.83/3.50  fof(f7,axiom,(
% 22.83/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f22,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(ennf_transformation,[],[f7])).
% 22.83/3.50  
% 22.83/3.50  fof(f23,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f22])).
% 22.83/3.50  
% 22.83/3.50  fof(f32,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(nnf_transformation,[],[f23])).
% 22.83/3.50  
% 22.83/3.50  fof(f33,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(rectify,[],[f32])).
% 22.83/3.50  
% 22.83/3.50  fof(f34,plain,(
% 22.83/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f35,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 22.83/3.50  
% 22.83/3.50  fof(f58,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f35])).
% 22.83/3.50  
% 22.83/3.50  fof(f12,conjecture,(
% 22.83/3.50    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f13,negated_conjecture,(
% 22.83/3.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 22.83/3.50    inference(negated_conjecture,[],[f12])).
% 22.83/3.50  
% 22.83/3.50  fof(f14,plain,(
% 22.83/3.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 22.83/3.50    inference(rectify,[],[f13])).
% 22.83/3.50  
% 22.83/3.50  fof(f16,plain,(
% 22.83/3.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 22.83/3.50    inference(pure_predicate_removal,[],[f14])).
% 22.83/3.50  
% 22.83/3.50  fof(f17,plain,(
% 22.83/3.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 22.83/3.50    inference(pure_predicate_removal,[],[f16])).
% 22.83/3.50  
% 22.83/3.50  fof(f30,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 22.83/3.50    inference(ennf_transformation,[],[f17])).
% 22.83/3.50  
% 22.83/3.50  fof(f31,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f30])).
% 22.83/3.50  
% 22.83/3.50  fof(f41,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 22.83/3.50    inference(nnf_transformation,[],[f31])).
% 22.83/3.50  
% 22.83/3.50  fof(f42,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f41])).
% 22.83/3.50  
% 22.83/3.50  fof(f43,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 22.83/3.50    inference(rectify,[],[f42])).
% 22.83/3.50  
% 22.83/3.50  fof(f48,plain,(
% 22.83/3.50    ( ! [X0,X1] : (! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k2_yellow_0(X0,sK6(X5)) = X5 & r2_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f47,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r1_lattice3(X0,X2,sK5) | ~r1_lattice3(X0,X1,sK5)) & (r1_lattice3(X0,X2,sK5) | r1_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f46,plain,(
% 22.83/3.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r1_lattice3(X0,sK4,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,sK4,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f45,plain,(
% 22.83/3.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,sK3,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f44,plain,(
% 22.83/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK2,X2,X3) | ~r1_lattice3(sK2,X1,X3)) & (r1_lattice3(sK2,X2,X3) | r1_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK2,X6) = X5 & r2_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f49,plain,(
% 22.83/3.50    ((((~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)) & (r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK2,sK6(X5)) = X5 & r2_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 22.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).
% 22.83/3.50  
% 22.83/3.50  fof(f74,plain,(
% 22.83/3.50    l1_orders_2(sK2)),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f3,axiom,(
% 22.83/3.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f18,plain,(
% 22.83/3.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 22.83/3.50    inference(ennf_transformation,[],[f3])).
% 22.83/3.50  
% 22.83/3.50  fof(f52,plain,(
% 22.83/3.50    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f18])).
% 22.83/3.50  
% 22.83/3.50  fof(f6,axiom,(
% 22.83/3.50    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f55,plain,(
% 22.83/3.50    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f6])).
% 22.83/3.50  
% 22.83/3.50  fof(f82,plain,(
% 22.83/3.50    ( ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f76,plain,(
% 22.83/3.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f5,axiom,(
% 22.83/3.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f20,plain,(
% 22.83/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 22.83/3.50    inference(ennf_transformation,[],[f5])).
% 22.83/3.50  
% 22.83/3.50  fof(f21,plain,(
% 22.83/3.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 22.83/3.50    inference(flattening,[],[f20])).
% 22.83/3.50  
% 22.83/3.50  fof(f54,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f21])).
% 22.83/3.50  
% 22.83/3.50  fof(f8,axiom,(
% 22.83/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f24,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(ennf_transformation,[],[f8])).
% 22.83/3.50  
% 22.83/3.50  fof(f25,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f24])).
% 22.83/3.50  
% 22.83/3.50  fof(f36,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(nnf_transformation,[],[f25])).
% 22.83/3.50  
% 22.83/3.50  fof(f37,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f36])).
% 22.83/3.50  
% 22.83/3.50  fof(f38,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(rectify,[],[f37])).
% 22.83/3.50  
% 22.83/3.50  fof(f39,plain,(
% 22.83/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 22.83/3.50    introduced(choice_axiom,[])).
% 22.83/3.50  
% 22.83/3.50  fof(f40,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 22.83/3.50  
% 22.83/3.50  fof(f60,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f40])).
% 22.83/3.50  
% 22.83/3.50  fof(f87,plain,(
% 22.83/3.50    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(equality_resolution,[],[f60])).
% 22.83/3.50  
% 22.83/3.50  fof(f83,plain,(
% 22.83/3.50    m1_subset_1(sK5,u1_struct_0(sK2))),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f9,axiom,(
% 22.83/3.50    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f26,plain,(
% 22.83/3.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 22.83/3.50    inference(ennf_transformation,[],[f9])).
% 22.83/3.50  
% 22.83/3.50  fof(f27,plain,(
% 22.83/3.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 22.83/3.50    inference(flattening,[],[f26])).
% 22.83/3.50  
% 22.83/3.50  fof(f65,plain,(
% 22.83/3.50    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f27])).
% 22.83/3.50  
% 22.83/3.50  fof(f73,plain,(
% 22.83/3.50    v4_orders_2(sK2)),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f84,plain,(
% 22.83/3.50    r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f61,plain,(
% 22.83/3.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f40])).
% 22.83/3.50  
% 22.83/3.50  fof(f86,plain,(
% 22.83/3.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(equality_resolution,[],[f61])).
% 22.83/3.50  
% 22.83/3.50  fof(f10,axiom,(
% 22.83/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f28,plain,(
% 22.83/3.50    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(ennf_transformation,[],[f10])).
% 22.83/3.50  
% 22.83/3.50  fof(f70,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f28])).
% 22.83/3.50  
% 22.83/3.50  fof(f4,axiom,(
% 22.83/3.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f15,plain,(
% 22.83/3.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 22.83/3.50    inference(unused_predicate_definition_removal,[],[f4])).
% 22.83/3.50  
% 22.83/3.50  fof(f19,plain,(
% 22.83/3.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 22.83/3.50    inference(ennf_transformation,[],[f15])).
% 22.83/3.50  
% 22.83/3.50  fof(f53,plain,(
% 22.83/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f19])).
% 22.83/3.50  
% 22.83/3.50  fof(f11,axiom,(
% 22.83/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f29,plain,(
% 22.83/3.50    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 22.83/3.50    inference(ennf_transformation,[],[f11])).
% 22.83/3.50  
% 22.83/3.50  fof(f72,plain,(
% 22.83/3.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f29])).
% 22.83/3.50  
% 22.83/3.50  fof(f57,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f35])).
% 22.83/3.50  
% 22.83/3.50  fof(f80,plain,(
% 22.83/3.50    ( ! [X5] : (r2_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f79,plain,(
% 22.83/3.50    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f71,plain,(
% 22.83/3.50    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f29])).
% 22.83/3.50  
% 22.83/3.50  fof(f59,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f35])).
% 22.83/3.50  
% 22.83/3.50  fof(f81,plain,(
% 22.83/3.50    ( ! [X5] : (k2_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f56,plain,(
% 22.83/3.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f35])).
% 22.83/3.50  
% 22.83/3.50  fof(f1,axiom,(
% 22.83/3.50    v1_xboole_0(k1_xboole_0)),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f50,plain,(
% 22.83/3.50    v1_xboole_0(k1_xboole_0)),
% 22.83/3.50    inference(cnf_transformation,[],[f1])).
% 22.83/3.50  
% 22.83/3.50  fof(f2,axiom,(
% 22.83/3.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 22.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 22.83/3.50  
% 22.83/3.50  fof(f51,plain,(
% 22.83/3.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 22.83/3.50    inference(cnf_transformation,[],[f2])).
% 22.83/3.50  
% 22.83/3.50  fof(f77,plain,(
% 22.83/3.50    ( ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f67,plain,(
% 22.83/3.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 22.83/3.50    inference(cnf_transformation,[],[f28])).
% 22.83/3.50  
% 22.83/3.50  fof(f75,plain,(
% 22.83/3.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  fof(f85,plain,(
% 22.83/3.50    ~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 22.83/3.50    inference(cnf_transformation,[],[f49])).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f58]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_34,negated_conjecture,
% 22.83/3.50      ( l1_orders_2(sK2) ),
% 22.83/3.50      inference(cnf_transformation,[],[f74]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_887,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_888,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,X1)
% 22.83/3.50      | r2_hidden(sK0(sK2,X0,X1),X0)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_887]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3691,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 22.83/3.50      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2,plain,
% 22.83/3.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f52]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3719,plain,
% 22.83/3.50      ( r2_hidden(X0,X1) != iProver_top
% 22.83/3.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5,plain,
% 22.83/3.50      ( v1_finset_1(k1_tarski(X0)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f55]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_26,negated_conjecture,
% 22.83/3.50      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 22.83/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 22.83/3.50      | ~ v1_finset_1(X0)
% 22.83/3.50      | k1_xboole_0 = X0 ),
% 22.83/3.50      inference(cnf_transformation,[],[f82]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_594,plain,
% 22.83/3.50      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 22.83/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 22.83/3.50      | k1_tarski(X1) != X0
% 22.83/3.50      | k1_xboole_0 = X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_5,c_26]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_595,plain,
% 22.83/3.50      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
% 22.83/3.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 22.83/3.50      | k1_xboole_0 = k1_tarski(X0) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_594]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3706,plain,
% 22.83/3.50      ( k1_xboole_0 = k1_tarski(X0)
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top
% 22.83/3.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_32,negated_conjecture,
% 22.83/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.83/3.50      inference(cnf_transformation,[],[f76]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3711,plain,
% 22.83/3.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4,plain,
% 22.83/3.50      ( ~ r2_hidden(X0,X1)
% 22.83/3.50      | m1_subset_1(X0,X2)
% 22.83/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f54]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3718,plain,
% 22.83/3.50      ( r2_hidden(X0,X1) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,X2) = iProver_top
% 22.83/3.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4255,plain,
% 22.83/3.50      ( r2_hidden(X0,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3711,c_3718]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_14,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 22.83/3.50      | ~ r2_yellow_0(X0,X1)
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f87]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_752,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 22.83/3.50      | ~ r2_yellow_0(X0,X1)
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_753,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 22.83/3.50      | ~ r2_yellow_0(sK2,X0)
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_752]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3698,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X0) != iProver_top
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4718,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X0) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_3698]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_25,negated_conjecture,
% 22.83/3.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f83]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3715,plain,
% 22.83/3.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_16,plain,
% 22.83/3.50      ( ~ r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,X3,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ v4_orders_2(X0)
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f65]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_35,negated_conjecture,
% 22.83/3.50      ( v4_orders_2(sK2) ),
% 22.83/3.50      inference(cnf_transformation,[],[f73]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_521,plain,
% 22.83/3.50      ( ~ r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,X3,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0)
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_522,plain,
% 22.83/3.50      ( ~ r1_orders_2(sK2,X0,X1)
% 22.83/3.50      | ~ r1_lattice3(sK2,X2,X1)
% 22.83/3.50      | r1_lattice3(sK2,X2,X0)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.83/3.50      | ~ l1_orders_2(sK2) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_521]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_524,plain,
% 22.83/3.50      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | r1_lattice3(sK2,X2,X0)
% 22.83/3.50      | ~ r1_lattice3(sK2,X2,X1)
% 22.83/3.50      | ~ r1_orders_2(sK2,X0,X1) ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_522,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_525,plain,
% 22.83/3.50      ( ~ r1_orders_2(sK2,X0,X1)
% 22.83/3.50      | ~ r1_lattice3(sK2,X2,X1)
% 22.83/3.50      | r1_lattice3(sK2,X2,X0)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(renaming,[status(thm)],[c_524]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3709,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X2,X1) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X2,X0) = iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6872,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X0) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,sK5) = iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3715,c_3709]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6929,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X0) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,sK5) = iProver_top
% 22.83/3.50      | r2_hidden(X0,sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_6872]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_10964,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X0,sK5) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X0) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4718,c_6929]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_24,negated_conjecture,
% 22.83/3.50      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 22.83/3.50      inference(cnf_transformation,[],[f84]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3716,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_13,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 22.83/3.50      | ~ r1_lattice3(X0,X2,X1)
% 22.83/3.50      | ~ r2_yellow_0(X0,X2)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f86]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_767,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 22.83/3.50      | ~ r1_lattice3(X0,X2,X1)
% 22.83/3.50      | ~ r2_yellow_0(X0,X2)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_768,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
% 22.83/3.50      | ~ r1_lattice3(sK2,X1,X0)
% 22.83/3.50      | ~ r2_yellow_0(sK2,X1)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_767]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3697,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1)) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X0) != iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X1) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7441,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1)) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X0) != iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X1) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_3697]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_17,plain,
% 22.83/3.50      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 22.83/3.50      | ~ r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f70]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_734,plain,
% 22.83/3.50      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 22.83/3.50      | ~ r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_735,plain,
% 22.83/3.50      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 22.83/3.50      | ~ r1_orders_2(sK2,X0,X1)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_734]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3699,plain,
% 22.83/3.50      ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,X0,X1) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3,plain,
% 22.83/3.50      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f53]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_21,plain,
% 22.83/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ r1_tarski(X3,X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f72]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_490,plain,
% 22.83/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 22.83/3.50      | ~ l1_orders_2(X0)
% 22.83/3.50      | X3 != X4
% 22.83/3.50      | X1 != X5 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_491,plain,
% 22.83/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_490]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_648,plain,
% 22.83/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 22.83/3.50      | r2_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_491,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_649,plain,
% 22.83/3.50      ( ~ r2_lattice3(sK2,X0,X1)
% 22.83/3.50      | r2_lattice3(sK2,X2,X1)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_648]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3704,plain,
% 22.83/3.50      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 22.83/3.50      | r2_lattice3(sK2,X2,X1) = iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5241,plain,
% 22.83/3.50      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 22.83/3.50      | r2_lattice3(sK2,X2,X1) = iProver_top
% 22.83/3.50      | r2_hidden(X1,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_3704]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_10511,plain,
% 22.83/3.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,X2,X1) != iProver_top
% 22.83/3.50      | r2_hidden(X1,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,k1_zfmisc_1(k1_tarski(X2))) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3699,c_5241]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_24686,plain,
% 22.83/3.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,X2,X1) != iProver_top
% 22.83/3.50      | r2_hidden(X1,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,k1_zfmisc_1(k1_tarski(X2))) != iProver_top ),
% 22.83/3.50      inference(forward_subsumption_resolution,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_10511,c_4255]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_24688,plain,
% 22.83/3.50      ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,X2,X1) != iProver_top
% 22.83/3.50      | r2_hidden(X0,k1_tarski(X2)) != iProver_top
% 22.83/3.50      | r2_hidden(X1,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3719,c_24686]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_26098,plain,
% 22.83/3.50      ( r2_lattice3(sK2,k1_tarski(X0),k2_yellow_0(sK2,X1)) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X2) != iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X1) != iProver_top
% 22.83/3.50      | r2_hidden(X0,k1_tarski(X2)) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_7441,c_24688]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_62683,plain,
% 22.83/3.50      ( r2_lattice3(sK2,k1_tarski(X0),k2_yellow_0(sK2,sK3)) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,sK3) != iProver_top
% 22.83/3.50      | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,sK3),sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3716,c_26098]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_58,plain,
% 22.83/3.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_59,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2951,plain,
% 22.83/3.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 22.83/3.50      theory(equality) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2962,plain,
% 22.83/3.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2951]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2943,plain,( X0 = X0 ),theory(equality) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2968,plain,
% 22.83/3.50      ( sK2 = sK2 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2943]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_8,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f57]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_872,plain,
% 22.83/3.50      ( r1_lattice3(X0,X1,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_873,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,X1)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.83/3.50      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_872]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4028,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,sK5)
% 22.83/3.50      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_873]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4163,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK4,sK5)
% 22.83/3.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4028]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4164,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 22.83/3.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4163]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4033,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,sK5)
% 22.83/3.50      | r2_hidden(sK0(sK2,X0,sK5),X0)
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_888]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4177,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK4,sK5)
% 22.83/3.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4033]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4178,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 22.83/3.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4177]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4189,plain,
% 22.83/3.50      ( sK5 = sK5 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2943]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_28,negated_conjecture,
% 22.83/3.50      ( r2_yellow_0(sK2,sK6(X0))
% 22.83/3.50      | ~ r2_hidden(X0,sK4)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f80]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4476,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 22.83/3.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_28]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4477,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
% 22.83/3.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4476]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_29,negated_conjecture,
% 22.83/3.50      ( ~ r2_hidden(X0,sK4)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f79]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4475,plain,
% 22.83/3.50      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 22.83/3.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 22.83/3.50      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_29]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4479,plain,
% 22.83/3.50      ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4475]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4637,plain,
% 22.83/3.50      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2943]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_22,plain,
% 22.83/3.50      ( ~ r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ r1_tarski(X3,X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f71]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_471,plain,
% 22.83/3.50      ( ~ r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 22.83/3.50      | ~ l1_orders_2(X0)
% 22.83/3.50      | X3 != X4
% 22.83/3.50      | X1 != X5 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_472,plain,
% 22.83/3.50      ( ~ r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_471]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_664,plain,
% 22.83/3.50      ( ~ r1_lattice3(X0,X1,X2)
% 22.83/3.50      | r1_lattice3(X0,X3,X2)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_472,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_665,plain,
% 22.83/3.50      ( ~ r1_lattice3(sK2,X0,X1)
% 22.83/3.50      | r1_lattice3(sK2,X2,X1)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_664]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4067,plain,
% 22.83/3.50      ( ~ r1_lattice3(sK2,X0,sK5)
% 22.83/3.50      | r1_lattice3(sK2,X1,sK5)
% 22.83/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_665]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4831,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 22.83/3.50      | ~ r1_lattice3(sK2,sK3,sK5)
% 22.83/3.50      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4067]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4832,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK3,sK5) != iProver_top
% 22.83/3.50      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4831]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2946,plain,
% 22.83/3.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 22.83/3.50      theory(equality) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4437,plain,
% 22.83/3.50      ( m1_subset_1(X0,X1)
% 22.83/3.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 22.83/3.50      | X0 != sK0(sK2,sK4,sK5)
% 22.83/3.50      | X1 != u1_struct_0(sK2) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2946]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4820,plain,
% 22.83/3.50      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
% 22.83/3.50      | X0 != u1_struct_0(sK2)
% 22.83/3.50      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4437]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5425,plain,
% 22.83/3.50      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 22.83/3.50      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 22.83/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4820]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5426,plain,
% 22.83/3.50      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 22.83/3.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 22.83/3.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_5425]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6,plain,
% 22.83/3.50      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 22.83/3.50      | r1_lattice3(X0,X2,X1)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f59]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_902,plain,
% 22.83/3.50      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 22.83/3.50      | r1_lattice3(X0,X2,X1)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_903,plain,
% 22.83/3.50      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 22.83/3.50      | r1_lattice3(sK2,X1,X0)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_902]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5710,plain,
% 22.83/3.50      ( ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5)
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_903]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_5711,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_5710]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4859,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 22.83/3.50      | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 22.83/3.50      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_768]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_8952,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 22.83/3.50      | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 22.83/3.50      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_4859]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_8953,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
% 22.83/3.50      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_8952]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_27,negated_conjecture,
% 22.83/3.50      ( ~ r2_hidden(X0,sK4)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | k2_yellow_0(sK2,sK6(X0)) = X0 ),
% 22.83/3.50      inference(cnf_transformation,[],[f81]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3714,plain,
% 22.83/3.50      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 22.83/3.50      | r2_hidden(X0,sK4) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4386,plain,
% 22.83/3.50      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 22.83/3.50      | r2_hidden(X0,sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_3714]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4884,plain,
% 22.83/3.50      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 22.83/3.50      | r1_lattice3(sK2,sK4,X0) = iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3691,c_4386]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_9655,plain,
% 22.83/3.50      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3715,c_4884]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2944,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6022,plain,
% 22.83/3.50      ( X0 != X1 | sK0(sK2,sK4,sK5) != X1 | sK0(sK2,sK4,sK5) = X0 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2944]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_11182,plain,
% 22.83/3.50      ( X0 != sK0(sK2,sK4,sK5)
% 22.83/3.50      | sK0(sK2,sK4,sK5) = X0
% 22.83/3.50      | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_6022]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_23115,plain,
% 22.83/3.50      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 22.83/3.50      | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_11182]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_2950,plain,
% 22.83/3.50      ( ~ r1_orders_2(X0,X1,X2)
% 22.83/3.50      | r1_orders_2(X3,X4,X5)
% 22.83/3.50      | X3 != X0
% 22.83/3.50      | X4 != X1
% 22.83/3.50      | X5 != X2 ),
% 22.83/3.50      theory(equality) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_11583,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 22.83/3.50      | X2 != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | X1 != sK5
% 22.83/3.50      | X0 != sK2 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_2950]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_16478,plain,
% 22.83/3.50      ( r1_orders_2(X0,sK5,X1)
% 22.83/3.50      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 22.83/3.50      | X1 != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | X0 != sK2
% 22.83/3.50      | sK5 != sK5 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_11583]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_61026,plain,
% 22.83/3.50      ( r1_orders_2(X0,sK5,sK0(sK2,sK4,sK5))
% 22.83/3.50      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 22.83/3.50      | X0 != sK2
% 22.83/3.50      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | sK5 != sK5 ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_16478]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_61027,plain,
% 22.83/3.50      ( X0 != sK2
% 22.83/3.50      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | sK5 != sK5
% 22.83/3.50      | r1_orders_2(X0,sK5,sK0(sK2,sK4,sK5)) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_61026]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_61029,plain,
% 22.83/3.50      ( sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 22.83/3.50      | sK5 != sK5
% 22.83/3.50      | sK2 != sK2
% 22.83/3.50      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) = iProver_top
% 22.83/3.50      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))) != iProver_top ),
% 22.83/3.50      inference(instantiation,[status(thm)],[c_61027]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_63772,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_62683,c_58,c_59,c_2962,c_2968,c_4164,c_4178,c_4189,
% 22.83/3.50                 c_4477,c_4479,c_4637,c_4832,c_5426,c_5711,c_8953,c_9655,
% 22.83/3.50                 c_23115,c_61029]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_9,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,X3,X1)
% 22.83/3.50      | ~ r2_hidden(X2,X3)
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f56]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_851,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,X3,X1)
% 22.83/3.50      | ~ r2_hidden(X2,X3)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_852,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,X1)
% 22.83/3.50      | ~ r1_lattice3(sK2,X2,X0)
% 22.83/3.50      | ~ r2_hidden(X1,X2)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_851]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3693,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X2,X0) != iProver_top
% 22.83/3.50      | r2_hidden(X1,X2) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6220,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,sK5) != iProver_top
% 22.83/3.50      | r2_hidden(X0,X1) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3715,c_3693]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_6406,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,sK5) != iProver_top
% 22.83/3.50      | r2_hidden(X0,X1) != iProver_top
% 22.83/3.50      | r2_hidden(X0,sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_4255,c_6220]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_63793,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 22.83/3.50      | r2_hidden(X0,sK4) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_63772,c_6406]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_79059,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,X0) != iProver_top
% 22.83/3.50      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 22.83/3.50      inference(forward_subsumption_resolution,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_10964,c_63793]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_79063,plain,
% 22.83/3.50      ( k1_tarski(X0) = k1_xboole_0
% 22.83/3.50      | r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
% 22.83/3.50      | r2_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 22.83/3.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3706,c_79059]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_0,plain,
% 22.83/3.50      ( v1_xboole_0(k1_xboole_0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f50]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_1,plain,
% 22.83/3.50      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 22.83/3.50      inference(cnf_transformation,[],[f51]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_465,plain,
% 22.83/3.50      ( k1_tarski(X0) != k1_xboole_0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4904,plain,
% 22.83/3.50      ( X0 != X1 | X1 = X0 ),
% 22.83/3.50      inference(resolution,[status(thm)],[c_2944,c_2943]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_31,negated_conjecture,
% 22.83/3.50      ( r2_yellow_0(sK2,X0)
% 22.83/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 22.83/3.50      | ~ v1_finset_1(X0)
% 22.83/3.50      | k1_xboole_0 = X0 ),
% 22.83/3.50      inference(cnf_transformation,[],[f77]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_579,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,X0)
% 22.83/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 22.83/3.50      | k1_tarski(X1) != X0
% 22.83/3.50      | k1_xboole_0 = X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_5,c_31]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_580,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,k1_tarski(X0))
% 22.83/3.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 22.83/3.50      | k1_xboole_0 = k1_tarski(X0) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_579]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7162,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,k1_tarski(X0))
% 22.83/3.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 22.83/3.50      | k1_tarski(X0) = k1_xboole_0 ),
% 22.83/3.50      inference(resolution,[status(thm)],[c_4904,c_580]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7642,plain,
% 22.83/3.50      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 22.83/3.50      | r2_yellow_0(sK2,k1_tarski(X0)) ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_7162,c_465]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7643,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,k1_tarski(X0))
% 22.83/3.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) ),
% 22.83/3.50      inference(renaming,[status(thm)],[c_7642]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_7644,plain,
% 22.83/3.50      ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 22.83/3.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_7643]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_79869,plain,
% 22.83/3.50      ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
% 22.83/3.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_79063,c_465,c_7644]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_79877,plain,
% 22.83/3.50      ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
% 22.83/3.50      | r2_hidden(X0,sK3) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3719,c_79869]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_20,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | ~ l1_orders_2(X0) ),
% 22.83/3.50      inference(cnf_transformation,[],[f67]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_680,plain,
% 22.83/3.50      ( r1_orders_2(X0,X1,X2)
% 22.83/3.50      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 22.83/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.83/3.50      | sK2 != X0 ),
% 22.83/3.50      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_681,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,X1)
% 22.83/3.50      | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
% 22.83/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.83/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 22.83/3.50      inference(unflattening,[status(thm)],[c_680]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3702,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 22.83/3.50      | r1_lattice3(sK2,k1_tarski(X1),X0) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_81695,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 22.83/3.50      | r2_hidden(X0,sK3) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_79877,c_3702]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_33,negated_conjecture,
% 22.83/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.83/3.50      inference(cnf_transformation,[],[f75]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3710,plain,
% 22.83/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_4256,plain,
% 22.83/3.50      ( r2_hidden(X0,sK3) != iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3710,c_3718]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_83212,plain,
% 22.83/3.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 22.83/3.50      | r2_hidden(X0,sK3) != iProver_top ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_81695,c_58,c_4256]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_3690,plain,
% 22.83/3.50      ( r1_orders_2(sK2,X0,sK0(sK2,X1,X0)) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X1,X0) = iProver_top
% 22.83/3.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_83231,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 22.83/3.50      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_83212,c_3690]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_83443,plain,
% 22.83/3.50      ( r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,X0,sK5) = iProver_top ),
% 22.83/3.50      inference(global_propositional_subsumption,
% 22.83/3.50                [status(thm)],
% 22.83/3.50                [c_83231,c_58]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_83444,plain,
% 22.83/3.50      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 22.83/3.50      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
% 22.83/3.50      inference(renaming,[status(thm)],[c_83443]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_83451,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 22.83/3.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 22.83/3.50      inference(superposition,[status(thm)],[c_3691,c_83444]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_23,negated_conjecture,
% 22.83/3.50      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 22.83/3.50      inference(cnf_transformation,[],[f85]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(c_60,plain,
% 22.83/3.50      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 22.83/3.50      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 22.83/3.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 22.83/3.50  
% 22.83/3.50  cnf(contradiction,plain,
% 22.83/3.50      ( $false ),
% 22.83/3.50      inference(minisat,[status(thm)],[c_83451,c_63772,c_60,c_58]) ).
% 22.83/3.50  
% 22.83/3.50  
% 22.83/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 22.83/3.50  
% 22.83/3.50  ------                               Statistics
% 22.83/3.50  
% 22.83/3.50  ------ Selected
% 22.83/3.50  
% 22.83/3.50  total_time:                             2.593
% 22.83/3.50  
%------------------------------------------------------------------------------
