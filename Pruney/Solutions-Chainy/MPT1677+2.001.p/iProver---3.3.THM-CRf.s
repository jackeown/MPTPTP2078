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
% DateTime   : Thu Dec  3 12:21:09 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :  221 (1792 expanded)
%              Number of clauses        :  140 ( 371 expanded)
%              Number of leaves         :   24 ( 489 expanded)
%              Depth                    :   27
%              Number of atoms          : 1149 (29270 expanded)
%              Number of equality atoms :  253 (4065 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

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
    inference(pure_predicate_removal,[],[f15])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f44,f49,f48,f47,f46,f45])).

fof(f78,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X7] :
      ( r2_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    ! [X5] :
      ( k2_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X5] :
      ( r2_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3331,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4492,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK2,sK5,X3)
    | X3 != X2
    | sK5 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_5120,plain,
    ( ~ r1_orders_2(X0,sK5,X1)
    | r1_orders_2(sK2,sK5,X2)
    | X2 != X1
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_4492])).

cnf(c_6352,plain,
    ( r1_orders_2(sK2,sK5,X0)
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X1))
    | X0 != k2_yellow_0(sK2,X1)
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5120])).

cnf(c_35429,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6352])).

cnf(c_25,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_807,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_808,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_tarski(X2,X0) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_4374,plain,
    ( ~ r1_lattice3(sK2,X0,sK5)
    | r1_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_11389,plain,
    ( ~ r1_lattice3(sK2,X0,sK5)
    | r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_4374])).

cnf(c_24555,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_11389])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1041,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_37])).

cnf(c_1042,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1041])).

cnf(c_4140,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_27,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4166,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4165,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4153,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_5517,plain,
    ( r1_lattice3(sK2,X0,sK5) != iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4165,c_4153])).

cnf(c_5569,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_5517])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4160,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4168,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5061,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4160,c_4168])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1005,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_37])).

cnf(c_1006,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_4142,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_6030,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,X1,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4165,c_4142])).

cnf(c_6050,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,X1,sK5) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5061,c_6030])).

cnf(c_7217,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5569,c_6050])).

cnf(c_61,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4255,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4256,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4255])).

cnf(c_23,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_839,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_37])).

cnf(c_840,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_4300,plain,
    ( r1_orders_2(sK2,sK5,X0)
    | ~ r1_lattice3(sK2,k1_tarski(X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_4301,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4300])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4544,plain,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4545,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k1_tarski(X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4544])).

cnf(c_4172,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4170,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,negated_conjecture,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_589,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_590,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_4157,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_5386,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4170,c_4157])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_525,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_5391,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5386,c_525])).

cnf(c_5397,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_5391])).

cnf(c_7218,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_6050])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_605,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_4156,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_17,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_911,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_912,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_4147,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_6052,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) = iProver_top
    | r1_lattice3(sK2,X1,sK5) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4147,c_6030])).

cnf(c_6335,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0))) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4156,c_6052])).

cnf(c_18793,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0))) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6335,c_525])).

cnf(c_16,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_233,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_234,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_795,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_234,c_37])).

cnf(c_796,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_4154,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_531,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_532,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,X2,X0)
    | ~ r1_lattice3(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_37])).

cnf(c_535,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_4159,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,X1) != iProver_top
    | r1_lattice3(sK2,X2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_6235,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4165,c_4159])).

cnf(c_6278,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
    | r1_lattice3(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | r1_lattice3(sK2,X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4147,c_6235])).

cnf(c_6673,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
    | r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_6278])).

cnf(c_18821,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18793,c_6673])).

cnf(c_19989,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7217,c_61,c_4256,c_4301,c_4545,c_5061,c_5397,c_7218,c_18821])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1056,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_37])).

cnf(c_1057,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1056])).

cnf(c_4139,plain,
    ( r1_orders_2(sK2,X0,sK0(sK2,X1,X0)) != iProver_top
    | r1_lattice3(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_20003,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19989,c_4139])).

cnf(c_20213,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20003,c_61])).

cnf(c_20219,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4140,c_20213])).

cnf(c_20220,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20219])).

cnf(c_3330,plain,
    ( X0 != X1
    | sK0(X0,X2,X3) = sK0(X1,X2,X3) ),
    theory(equality)).

cnf(c_13283,plain,
    ( sK0(sK2,sK4,sK5) = sK0(X0,sK4,sK5)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3330])).

cnf(c_13284,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_13283])).

cnf(c_15,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_920,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_921,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
    | ~ r1_lattice3(sK2,X1,X0)
    | ~ r2_yellow_0(sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_930,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
    | ~ r1_lattice3(sK2,X1,X0)
    | ~ r2_yellow_0(sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_921,c_912])).

cnf(c_6807,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_8111,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_3324,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5582,plain,
    ( X0 != X1
    | X0 = k2_yellow_0(sK2,X2)
    | k2_yellow_0(sK2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_3324])).

cnf(c_6758,plain,
    ( X0 != sK0(sK2,sK4,sK5)
    | X0 = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5582])).

cnf(c_7944,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6758])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4161,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5060,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_4168])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | k2_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4164,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5142,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5060,c_4164])).

cnf(c_5351,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r1_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4140,c_5142])).

cnf(c_6832,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4165,c_5351])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6763,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3323,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5561,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3323])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5303,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5304,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4348,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_4508,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_4348])).

cnf(c_4360,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,X0,sK5))
    | r1_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_4473,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4360])).

cnf(c_10,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1026,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_37])).

cnf(c_1027,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_4280,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_4470,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4280])).

cnf(c_3350,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3323])).

cnf(c_26,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_63,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35429,c_24555,c_20220,c_20219,c_13284,c_8111,c_7944,c_6832,c_6763,c_5561,c_5303,c_5304,c_4508,c_4473,c_4470,c_3350,c_63,c_26,c_61,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.80/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.80/2.00  
% 11.80/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.80/2.00  
% 11.80/2.00  ------  iProver source info
% 11.80/2.00  
% 11.80/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.80/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.80/2.00  git: non_committed_changes: false
% 11.80/2.00  git: last_make_outside_of_git: false
% 11.80/2.00  
% 11.80/2.00  ------ 
% 11.80/2.00  
% 11.80/2.00  ------ Input Options
% 11.80/2.00  
% 11.80/2.00  --out_options                           all
% 11.80/2.00  --tptp_safe_out                         true
% 11.80/2.00  --problem_path                          ""
% 11.80/2.00  --include_path                          ""
% 11.80/2.00  --clausifier                            res/vclausify_rel
% 11.80/2.00  --clausifier_options                    ""
% 11.80/2.00  --stdin                                 false
% 11.80/2.00  --stats_out                             all
% 11.80/2.00  
% 11.80/2.00  ------ General Options
% 11.80/2.00  
% 11.80/2.00  --fof                                   false
% 11.80/2.00  --time_out_real                         305.
% 11.80/2.00  --time_out_virtual                      -1.
% 11.80/2.00  --symbol_type_check                     false
% 11.80/2.00  --clausify_out                          false
% 11.80/2.00  --sig_cnt_out                           false
% 11.80/2.00  --trig_cnt_out                          false
% 11.80/2.00  --trig_cnt_out_tolerance                1.
% 11.80/2.00  --trig_cnt_out_sk_spl                   false
% 11.80/2.00  --abstr_cl_out                          false
% 11.80/2.00  
% 11.80/2.00  ------ Global Options
% 11.80/2.00  
% 11.80/2.00  --schedule                              default
% 11.80/2.00  --add_important_lit                     false
% 11.80/2.00  --prop_solver_per_cl                    1000
% 11.80/2.00  --min_unsat_core                        false
% 11.80/2.00  --soft_assumptions                      false
% 11.80/2.00  --soft_lemma_size                       3
% 11.80/2.00  --prop_impl_unit_size                   0
% 11.80/2.00  --prop_impl_unit                        []
% 11.80/2.00  --share_sel_clauses                     true
% 11.80/2.00  --reset_solvers                         false
% 11.80/2.00  --bc_imp_inh                            [conj_cone]
% 11.80/2.00  --conj_cone_tolerance                   3.
% 11.80/2.00  --extra_neg_conj                        none
% 11.80/2.00  --large_theory_mode                     true
% 11.80/2.00  --prolific_symb_bound                   200
% 11.80/2.00  --lt_threshold                          2000
% 11.80/2.00  --clause_weak_htbl                      true
% 11.80/2.00  --gc_record_bc_elim                     false
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing Options
% 11.80/2.00  
% 11.80/2.00  --preprocessing_flag                    true
% 11.80/2.00  --time_out_prep_mult                    0.1
% 11.80/2.00  --splitting_mode                        input
% 11.80/2.00  --splitting_grd                         true
% 11.80/2.00  --splitting_cvd                         false
% 11.80/2.00  --splitting_cvd_svl                     false
% 11.80/2.00  --splitting_nvd                         32
% 11.80/2.00  --sub_typing                            true
% 11.80/2.00  --prep_gs_sim                           true
% 11.80/2.00  --prep_unflatten                        true
% 11.80/2.00  --prep_res_sim                          true
% 11.80/2.00  --prep_upred                            true
% 11.80/2.00  --prep_sem_filter                       exhaustive
% 11.80/2.00  --prep_sem_filter_out                   false
% 11.80/2.00  --pred_elim                             true
% 11.80/2.00  --res_sim_input                         true
% 11.80/2.00  --eq_ax_congr_red                       true
% 11.80/2.00  --pure_diseq_elim                       true
% 11.80/2.00  --brand_transform                       false
% 11.80/2.00  --non_eq_to_eq                          false
% 11.80/2.00  --prep_def_merge                        true
% 11.80/2.00  --prep_def_merge_prop_impl              false
% 11.80/2.00  --prep_def_merge_mbd                    true
% 11.80/2.00  --prep_def_merge_tr_red                 false
% 11.80/2.00  --prep_def_merge_tr_cl                  false
% 11.80/2.00  --smt_preprocessing                     true
% 11.80/2.00  --smt_ac_axioms                         fast
% 11.80/2.00  --preprocessed_out                      false
% 11.80/2.00  --preprocessed_stats                    false
% 11.80/2.00  
% 11.80/2.00  ------ Abstraction refinement Options
% 11.80/2.00  
% 11.80/2.00  --abstr_ref                             []
% 11.80/2.00  --abstr_ref_prep                        false
% 11.80/2.00  --abstr_ref_until_sat                   false
% 11.80/2.00  --abstr_ref_sig_restrict                funpre
% 11.80/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/2.00  --abstr_ref_under                       []
% 11.80/2.00  
% 11.80/2.00  ------ SAT Options
% 11.80/2.00  
% 11.80/2.00  --sat_mode                              false
% 11.80/2.00  --sat_fm_restart_options                ""
% 11.80/2.00  --sat_gr_def                            false
% 11.80/2.00  --sat_epr_types                         true
% 11.80/2.00  --sat_non_cyclic_types                  false
% 11.80/2.00  --sat_finite_models                     false
% 11.80/2.00  --sat_fm_lemmas                         false
% 11.80/2.00  --sat_fm_prep                           false
% 11.80/2.00  --sat_fm_uc_incr                        true
% 11.80/2.00  --sat_out_model                         small
% 11.80/2.00  --sat_out_clauses                       false
% 11.80/2.00  
% 11.80/2.00  ------ QBF Options
% 11.80/2.00  
% 11.80/2.00  --qbf_mode                              false
% 11.80/2.00  --qbf_elim_univ                         false
% 11.80/2.00  --qbf_dom_inst                          none
% 11.80/2.00  --qbf_dom_pre_inst                      false
% 11.80/2.00  --qbf_sk_in                             false
% 11.80/2.00  --qbf_pred_elim                         true
% 11.80/2.00  --qbf_split                             512
% 11.80/2.00  
% 11.80/2.00  ------ BMC1 Options
% 11.80/2.00  
% 11.80/2.00  --bmc1_incremental                      false
% 11.80/2.00  --bmc1_axioms                           reachable_all
% 11.80/2.00  --bmc1_min_bound                        0
% 11.80/2.00  --bmc1_max_bound                        -1
% 11.80/2.00  --bmc1_max_bound_default                -1
% 11.80/2.00  --bmc1_symbol_reachability              true
% 11.80/2.00  --bmc1_property_lemmas                  false
% 11.80/2.00  --bmc1_k_induction                      false
% 11.80/2.00  --bmc1_non_equiv_states                 false
% 11.80/2.00  --bmc1_deadlock                         false
% 11.80/2.00  --bmc1_ucm                              false
% 11.80/2.00  --bmc1_add_unsat_core                   none
% 11.80/2.00  --bmc1_unsat_core_children              false
% 11.80/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/2.00  --bmc1_out_stat                         full
% 11.80/2.00  --bmc1_ground_init                      false
% 11.80/2.00  --bmc1_pre_inst_next_state              false
% 11.80/2.00  --bmc1_pre_inst_state                   false
% 11.80/2.00  --bmc1_pre_inst_reach_state             false
% 11.80/2.00  --bmc1_out_unsat_core                   false
% 11.80/2.00  --bmc1_aig_witness_out                  false
% 11.80/2.00  --bmc1_verbose                          false
% 11.80/2.00  --bmc1_dump_clauses_tptp                false
% 11.80/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.80/2.00  --bmc1_dump_file                        -
% 11.80/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.80/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.80/2.00  --bmc1_ucm_extend_mode                  1
% 11.80/2.00  --bmc1_ucm_init_mode                    2
% 11.80/2.00  --bmc1_ucm_cone_mode                    none
% 11.80/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.80/2.00  --bmc1_ucm_relax_model                  4
% 11.80/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.80/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/2.00  --bmc1_ucm_layered_model                none
% 11.80/2.00  --bmc1_ucm_max_lemma_size               10
% 11.80/2.00  
% 11.80/2.00  ------ AIG Options
% 11.80/2.00  
% 11.80/2.00  --aig_mode                              false
% 11.80/2.00  
% 11.80/2.00  ------ Instantiation Options
% 11.80/2.00  
% 11.80/2.00  --instantiation_flag                    true
% 11.80/2.00  --inst_sos_flag                         true
% 11.80/2.00  --inst_sos_phase                        true
% 11.80/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/2.00  --inst_lit_sel_side                     num_symb
% 11.80/2.00  --inst_solver_per_active                1400
% 11.80/2.00  --inst_solver_calls_frac                1.
% 11.80/2.00  --inst_passive_queue_type               priority_queues
% 11.80/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/2.00  --inst_passive_queues_freq              [25;2]
% 11.80/2.00  --inst_dismatching                      true
% 11.80/2.00  --inst_eager_unprocessed_to_passive     true
% 11.80/2.00  --inst_prop_sim_given                   true
% 11.80/2.00  --inst_prop_sim_new                     false
% 11.80/2.00  --inst_subs_new                         false
% 11.80/2.00  --inst_eq_res_simp                      false
% 11.80/2.00  --inst_subs_given                       false
% 11.80/2.00  --inst_orphan_elimination               true
% 11.80/2.00  --inst_learning_loop_flag               true
% 11.80/2.00  --inst_learning_start                   3000
% 11.80/2.00  --inst_learning_factor                  2
% 11.80/2.00  --inst_start_prop_sim_after_learn       3
% 11.80/2.00  --inst_sel_renew                        solver
% 11.80/2.00  --inst_lit_activity_flag                true
% 11.80/2.00  --inst_restr_to_given                   false
% 11.80/2.00  --inst_activity_threshold               500
% 11.80/2.00  --inst_out_proof                        true
% 11.80/2.00  
% 11.80/2.00  ------ Resolution Options
% 11.80/2.00  
% 11.80/2.00  --resolution_flag                       true
% 11.80/2.00  --res_lit_sel                           adaptive
% 11.80/2.00  --res_lit_sel_side                      none
% 11.80/2.00  --res_ordering                          kbo
% 11.80/2.00  --res_to_prop_solver                    active
% 11.80/2.00  --res_prop_simpl_new                    false
% 11.80/2.00  --res_prop_simpl_given                  true
% 11.80/2.00  --res_passive_queue_type                priority_queues
% 11.80/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/2.00  --res_passive_queues_freq               [15;5]
% 11.80/2.00  --res_forward_subs                      full
% 11.80/2.00  --res_backward_subs                     full
% 11.80/2.00  --res_forward_subs_resolution           true
% 11.80/2.00  --res_backward_subs_resolution          true
% 11.80/2.00  --res_orphan_elimination                true
% 11.80/2.00  --res_time_limit                        2.
% 11.80/2.00  --res_out_proof                         true
% 11.80/2.00  
% 11.80/2.00  ------ Superposition Options
% 11.80/2.00  
% 11.80/2.00  --superposition_flag                    true
% 11.80/2.00  --sup_passive_queue_type                priority_queues
% 11.80/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.80/2.00  --demod_completeness_check              fast
% 11.80/2.00  --demod_use_ground                      true
% 11.80/2.00  --sup_to_prop_solver                    passive
% 11.80/2.00  --sup_prop_simpl_new                    true
% 11.80/2.00  --sup_prop_simpl_given                  true
% 11.80/2.00  --sup_fun_splitting                     true
% 11.80/2.00  --sup_smt_interval                      50000
% 11.80/2.00  
% 11.80/2.00  ------ Superposition Simplification Setup
% 11.80/2.00  
% 11.80/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/2.00  --sup_immed_triv                        [TrivRules]
% 11.80/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_immed_bw_main                     []
% 11.80/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_input_bw                          []
% 11.80/2.00  
% 11.80/2.00  ------ Combination Options
% 11.80/2.00  
% 11.80/2.00  --comb_res_mult                         3
% 11.80/2.00  --comb_sup_mult                         2
% 11.80/2.00  --comb_inst_mult                        10
% 11.80/2.00  
% 11.80/2.00  ------ Debug Options
% 11.80/2.00  
% 11.80/2.00  --dbg_backtrace                         false
% 11.80/2.00  --dbg_dump_prop_clauses                 false
% 11.80/2.00  --dbg_dump_prop_clauses_file            -
% 11.80/2.00  --dbg_out_stat                          false
% 11.80/2.00  ------ Parsing...
% 11.80/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/2.00  ------ Proving...
% 11.80/2.00  ------ Problem Properties 
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  clauses                                 35
% 11.80/2.00  conjectures                             8
% 11.80/2.00  EPR                                     2
% 11.80/2.00  Horn                                    27
% 11.80/2.00  unary                                   5
% 11.80/2.00  binary                                  7
% 11.80/2.00  lits                                    108
% 11.80/2.00  lits eq                                 8
% 11.80/2.00  fd_pure                                 0
% 11.80/2.00  fd_pseudo                               0
% 11.80/2.00  fd_cond                                 0
% 11.80/2.00  fd_pseudo_cond                          3
% 11.80/2.00  AC symbols                              0
% 11.80/2.00  
% 11.80/2.00  ------ Schedule dynamic 5 is on 
% 11.80/2.00  
% 11.80/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  ------ 
% 11.80/2.00  Current options:
% 11.80/2.00  ------ 
% 11.80/2.00  
% 11.80/2.00  ------ Input Options
% 11.80/2.00  
% 11.80/2.00  --out_options                           all
% 11.80/2.00  --tptp_safe_out                         true
% 11.80/2.00  --problem_path                          ""
% 11.80/2.00  --include_path                          ""
% 11.80/2.00  --clausifier                            res/vclausify_rel
% 11.80/2.00  --clausifier_options                    ""
% 11.80/2.00  --stdin                                 false
% 11.80/2.00  --stats_out                             all
% 11.80/2.00  
% 11.80/2.00  ------ General Options
% 11.80/2.00  
% 11.80/2.00  --fof                                   false
% 11.80/2.00  --time_out_real                         305.
% 11.80/2.00  --time_out_virtual                      -1.
% 11.80/2.00  --symbol_type_check                     false
% 11.80/2.00  --clausify_out                          false
% 11.80/2.00  --sig_cnt_out                           false
% 11.80/2.00  --trig_cnt_out                          false
% 11.80/2.00  --trig_cnt_out_tolerance                1.
% 11.80/2.00  --trig_cnt_out_sk_spl                   false
% 11.80/2.00  --abstr_cl_out                          false
% 11.80/2.00  
% 11.80/2.00  ------ Global Options
% 11.80/2.00  
% 11.80/2.00  --schedule                              default
% 11.80/2.00  --add_important_lit                     false
% 11.80/2.00  --prop_solver_per_cl                    1000
% 11.80/2.00  --min_unsat_core                        false
% 11.80/2.00  --soft_assumptions                      false
% 11.80/2.00  --soft_lemma_size                       3
% 11.80/2.00  --prop_impl_unit_size                   0
% 11.80/2.00  --prop_impl_unit                        []
% 11.80/2.00  --share_sel_clauses                     true
% 11.80/2.00  --reset_solvers                         false
% 11.80/2.00  --bc_imp_inh                            [conj_cone]
% 11.80/2.00  --conj_cone_tolerance                   3.
% 11.80/2.00  --extra_neg_conj                        none
% 11.80/2.00  --large_theory_mode                     true
% 11.80/2.00  --prolific_symb_bound                   200
% 11.80/2.00  --lt_threshold                          2000
% 11.80/2.00  --clause_weak_htbl                      true
% 11.80/2.00  --gc_record_bc_elim                     false
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing Options
% 11.80/2.00  
% 11.80/2.00  --preprocessing_flag                    true
% 11.80/2.00  --time_out_prep_mult                    0.1
% 11.80/2.00  --splitting_mode                        input
% 11.80/2.00  --splitting_grd                         true
% 11.80/2.00  --splitting_cvd                         false
% 11.80/2.00  --splitting_cvd_svl                     false
% 11.80/2.00  --splitting_nvd                         32
% 11.80/2.00  --sub_typing                            true
% 11.80/2.00  --prep_gs_sim                           true
% 11.80/2.00  --prep_unflatten                        true
% 11.80/2.00  --prep_res_sim                          true
% 11.80/2.00  --prep_upred                            true
% 11.80/2.00  --prep_sem_filter                       exhaustive
% 11.80/2.00  --prep_sem_filter_out                   false
% 11.80/2.00  --pred_elim                             true
% 11.80/2.00  --res_sim_input                         true
% 11.80/2.00  --eq_ax_congr_red                       true
% 11.80/2.00  --pure_diseq_elim                       true
% 11.80/2.00  --brand_transform                       false
% 11.80/2.00  --non_eq_to_eq                          false
% 11.80/2.00  --prep_def_merge                        true
% 11.80/2.00  --prep_def_merge_prop_impl              false
% 11.80/2.00  --prep_def_merge_mbd                    true
% 11.80/2.00  --prep_def_merge_tr_red                 false
% 11.80/2.00  --prep_def_merge_tr_cl                  false
% 11.80/2.00  --smt_preprocessing                     true
% 11.80/2.00  --smt_ac_axioms                         fast
% 11.80/2.00  --preprocessed_out                      false
% 11.80/2.00  --preprocessed_stats                    false
% 11.80/2.00  
% 11.80/2.00  ------ Abstraction refinement Options
% 11.80/2.00  
% 11.80/2.00  --abstr_ref                             []
% 11.80/2.00  --abstr_ref_prep                        false
% 11.80/2.00  --abstr_ref_until_sat                   false
% 11.80/2.00  --abstr_ref_sig_restrict                funpre
% 11.80/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/2.00  --abstr_ref_under                       []
% 11.80/2.00  
% 11.80/2.00  ------ SAT Options
% 11.80/2.00  
% 11.80/2.00  --sat_mode                              false
% 11.80/2.00  --sat_fm_restart_options                ""
% 11.80/2.00  --sat_gr_def                            false
% 11.80/2.00  --sat_epr_types                         true
% 11.80/2.00  --sat_non_cyclic_types                  false
% 11.80/2.00  --sat_finite_models                     false
% 11.80/2.00  --sat_fm_lemmas                         false
% 11.80/2.00  --sat_fm_prep                           false
% 11.80/2.00  --sat_fm_uc_incr                        true
% 11.80/2.00  --sat_out_model                         small
% 11.80/2.00  --sat_out_clauses                       false
% 11.80/2.00  
% 11.80/2.00  ------ QBF Options
% 11.80/2.00  
% 11.80/2.00  --qbf_mode                              false
% 11.80/2.00  --qbf_elim_univ                         false
% 11.80/2.00  --qbf_dom_inst                          none
% 11.80/2.00  --qbf_dom_pre_inst                      false
% 11.80/2.00  --qbf_sk_in                             false
% 11.80/2.00  --qbf_pred_elim                         true
% 11.80/2.00  --qbf_split                             512
% 11.80/2.00  
% 11.80/2.00  ------ BMC1 Options
% 11.80/2.00  
% 11.80/2.00  --bmc1_incremental                      false
% 11.80/2.00  --bmc1_axioms                           reachable_all
% 11.80/2.00  --bmc1_min_bound                        0
% 11.80/2.00  --bmc1_max_bound                        -1
% 11.80/2.00  --bmc1_max_bound_default                -1
% 11.80/2.00  --bmc1_symbol_reachability              true
% 11.80/2.00  --bmc1_property_lemmas                  false
% 11.80/2.00  --bmc1_k_induction                      false
% 11.80/2.00  --bmc1_non_equiv_states                 false
% 11.80/2.00  --bmc1_deadlock                         false
% 11.80/2.00  --bmc1_ucm                              false
% 11.80/2.00  --bmc1_add_unsat_core                   none
% 11.80/2.00  --bmc1_unsat_core_children              false
% 11.80/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/2.00  --bmc1_out_stat                         full
% 11.80/2.00  --bmc1_ground_init                      false
% 11.80/2.00  --bmc1_pre_inst_next_state              false
% 11.80/2.00  --bmc1_pre_inst_state                   false
% 11.80/2.00  --bmc1_pre_inst_reach_state             false
% 11.80/2.00  --bmc1_out_unsat_core                   false
% 11.80/2.00  --bmc1_aig_witness_out                  false
% 11.80/2.00  --bmc1_verbose                          false
% 11.80/2.00  --bmc1_dump_clauses_tptp                false
% 11.80/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.80/2.00  --bmc1_dump_file                        -
% 11.80/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.80/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.80/2.00  --bmc1_ucm_extend_mode                  1
% 11.80/2.00  --bmc1_ucm_init_mode                    2
% 11.80/2.00  --bmc1_ucm_cone_mode                    none
% 11.80/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.80/2.00  --bmc1_ucm_relax_model                  4
% 11.80/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.80/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/2.00  --bmc1_ucm_layered_model                none
% 11.80/2.00  --bmc1_ucm_max_lemma_size               10
% 11.80/2.00  
% 11.80/2.00  ------ AIG Options
% 11.80/2.00  
% 11.80/2.00  --aig_mode                              false
% 11.80/2.00  
% 11.80/2.00  ------ Instantiation Options
% 11.80/2.00  
% 11.80/2.00  --instantiation_flag                    true
% 11.80/2.00  --inst_sos_flag                         true
% 11.80/2.00  --inst_sos_phase                        true
% 11.80/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/2.00  --inst_lit_sel_side                     none
% 11.80/2.00  --inst_solver_per_active                1400
% 11.80/2.00  --inst_solver_calls_frac                1.
% 11.80/2.00  --inst_passive_queue_type               priority_queues
% 11.80/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/2.00  --inst_passive_queues_freq              [25;2]
% 11.80/2.00  --inst_dismatching                      true
% 11.80/2.00  --inst_eager_unprocessed_to_passive     true
% 11.80/2.00  --inst_prop_sim_given                   true
% 11.80/2.00  --inst_prop_sim_new                     false
% 11.80/2.00  --inst_subs_new                         false
% 11.80/2.00  --inst_eq_res_simp                      false
% 11.80/2.00  --inst_subs_given                       false
% 11.80/2.00  --inst_orphan_elimination               true
% 11.80/2.00  --inst_learning_loop_flag               true
% 11.80/2.00  --inst_learning_start                   3000
% 11.80/2.00  --inst_learning_factor                  2
% 11.80/2.00  --inst_start_prop_sim_after_learn       3
% 11.80/2.00  --inst_sel_renew                        solver
% 11.80/2.00  --inst_lit_activity_flag                true
% 11.80/2.00  --inst_restr_to_given                   false
% 11.80/2.00  --inst_activity_threshold               500
% 11.80/2.00  --inst_out_proof                        true
% 11.80/2.00  
% 11.80/2.00  ------ Resolution Options
% 11.80/2.00  
% 11.80/2.00  --resolution_flag                       false
% 11.80/2.00  --res_lit_sel                           adaptive
% 11.80/2.00  --res_lit_sel_side                      none
% 11.80/2.00  --res_ordering                          kbo
% 11.80/2.00  --res_to_prop_solver                    active
% 11.80/2.00  --res_prop_simpl_new                    false
% 11.80/2.00  --res_prop_simpl_given                  true
% 11.80/2.00  --res_passive_queue_type                priority_queues
% 11.80/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/2.00  --res_passive_queues_freq               [15;5]
% 11.80/2.00  --res_forward_subs                      full
% 11.80/2.00  --res_backward_subs                     full
% 11.80/2.00  --res_forward_subs_resolution           true
% 11.80/2.00  --res_backward_subs_resolution          true
% 11.80/2.00  --res_orphan_elimination                true
% 11.80/2.00  --res_time_limit                        2.
% 11.80/2.00  --res_out_proof                         true
% 11.80/2.00  
% 11.80/2.00  ------ Superposition Options
% 11.80/2.00  
% 11.80/2.00  --superposition_flag                    true
% 11.80/2.00  --sup_passive_queue_type                priority_queues
% 11.80/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.80/2.00  --demod_completeness_check              fast
% 11.80/2.00  --demod_use_ground                      true
% 11.80/2.00  --sup_to_prop_solver                    passive
% 11.80/2.00  --sup_prop_simpl_new                    true
% 11.80/2.00  --sup_prop_simpl_given                  true
% 11.80/2.00  --sup_fun_splitting                     true
% 11.80/2.00  --sup_smt_interval                      50000
% 11.80/2.00  
% 11.80/2.00  ------ Superposition Simplification Setup
% 11.80/2.00  
% 11.80/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/2.00  --sup_immed_triv                        [TrivRules]
% 11.80/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_immed_bw_main                     []
% 11.80/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/2.00  --sup_input_bw                          []
% 11.80/2.00  
% 11.80/2.00  ------ Combination Options
% 11.80/2.00  
% 11.80/2.00  --comb_res_mult                         3
% 11.80/2.00  --comb_sup_mult                         2
% 11.80/2.00  --comb_inst_mult                        10
% 11.80/2.00  
% 11.80/2.00  ------ Debug Options
% 11.80/2.00  
% 11.80/2.00  --dbg_backtrace                         false
% 11.80/2.00  --dbg_dump_prop_clauses                 false
% 11.80/2.00  --dbg_dump_prop_clauses_file            -
% 11.80/2.00  --dbg_out_stat                          false
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  ------ Proving...
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  % SZS status Theorem for theBenchmark.p
% 11.80/2.00  
% 11.80/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.80/2.00  
% 11.80/2.00  fof(f12,axiom,(
% 11.80/2.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f28,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(ennf_transformation,[],[f12])).
% 11.80/2.00  
% 11.80/2.00  fof(f75,plain,(
% 11.80/2.00    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f28])).
% 11.80/2.00  
% 11.80/2.00  fof(f13,conjecture,(
% 11.80/2.00    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f14,negated_conjecture,(
% 11.80/2.00    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 11.80/2.00    inference(negated_conjecture,[],[f13])).
% 11.80/2.00  
% 11.80/2.00  fof(f15,plain,(
% 11.80/2.00    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 11.80/2.00    inference(rectify,[],[f14])).
% 11.80/2.00  
% 11.80/2.00  fof(f16,plain,(
% 11.80/2.00    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 11.80/2.00    inference(pure_predicate_removal,[],[f15])).
% 11.80/2.00  
% 11.80/2.00  fof(f17,plain,(
% 11.80/2.00    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 11.80/2.00    inference(pure_predicate_removal,[],[f16])).
% 11.80/2.00  
% 11.80/2.00  fof(f29,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 11.80/2.00    inference(ennf_transformation,[],[f17])).
% 11.80/2.00  
% 11.80/2.00  fof(f30,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f29])).
% 11.80/2.00  
% 11.80/2.00  fof(f42,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 11.80/2.00    inference(nnf_transformation,[],[f30])).
% 11.80/2.00  
% 11.80/2.00  fof(f43,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f42])).
% 11.80/2.00  
% 11.80/2.00  fof(f44,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 11.80/2.00    inference(rectify,[],[f43])).
% 11.80/2.00  
% 11.80/2.00  fof(f49,plain,(
% 11.80/2.00    ( ! [X0,X1] : (! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k2_yellow_0(X0,sK6(X5)) = X5 & r2_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f48,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r1_lattice3(X0,X2,sK5) | ~r1_lattice3(X0,X1,sK5)) & (r1_lattice3(X0,X2,sK5) | r1_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f47,plain,(
% 11.80/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r1_lattice3(X0,sK4,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,sK4,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f46,plain,(
% 11.80/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,sK3,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f45,plain,(
% 11.80/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK2,X2,X3) | ~r1_lattice3(sK2,X1,X3)) & (r1_lattice3(sK2,X2,X3) | r1_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK2,X6) = X5 & r2_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f50,plain,(
% 11.80/2.00    ((((~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)) & (r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK2,sK6(X5)) = X5 & r2_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 11.80/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f44,f49,f48,f47,f46,f45])).
% 11.80/2.00  
% 11.80/2.00  fof(f78,plain,(
% 11.80/2.00    l1_orders_2(sK2)),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f7,axiom,(
% 11.80/2.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f20,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(ennf_transformation,[],[f7])).
% 11.80/2.00  
% 11.80/2.00  fof(f21,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f20])).
% 11.80/2.00  
% 11.80/2.00  fof(f33,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(nnf_transformation,[],[f21])).
% 11.80/2.00  
% 11.80/2.00  fof(f34,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(rectify,[],[f33])).
% 11.80/2.00  
% 11.80/2.00  fof(f35,plain,(
% 11.80/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f36,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 11.80/2.00  
% 11.80/2.00  fof(f61,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f36])).
% 11.80/2.00  
% 11.80/2.00  fof(f88,plain,(
% 11.80/2.00    r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f87,plain,(
% 11.80/2.00    m1_subset_1(sK5,u1_struct_0(sK2))),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f79,plain,(
% 11.80/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f5,axiom,(
% 11.80/2.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f18,plain,(
% 11.80/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.80/2.00    inference(ennf_transformation,[],[f5])).
% 11.80/2.00  
% 11.80/2.00  fof(f19,plain,(
% 11.80/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.80/2.00    inference(flattening,[],[f18])).
% 11.80/2.00  
% 11.80/2.00  fof(f57,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f19])).
% 11.80/2.00  
% 11.80/2.00  fof(f59,plain,(
% 11.80/2.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f36])).
% 11.80/2.00  
% 11.80/2.00  fof(f4,axiom,(
% 11.80/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f32,plain,(
% 11.80/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.80/2.00    inference(nnf_transformation,[],[f4])).
% 11.80/2.00  
% 11.80/2.00  fof(f56,plain,(
% 11.80/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f32])).
% 11.80/2.00  
% 11.80/2.00  fof(f11,axiom,(
% 11.80/2.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f27,plain,(
% 11.80/2.00    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(ennf_transformation,[],[f11])).
% 11.80/2.00  
% 11.80/2.00  fof(f71,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f27])).
% 11.80/2.00  
% 11.80/2.00  fof(f3,axiom,(
% 11.80/2.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f31,plain,(
% 11.80/2.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.80/2.00    inference(nnf_transformation,[],[f3])).
% 11.80/2.00  
% 11.80/2.00  fof(f54,plain,(
% 11.80/2.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f31])).
% 11.80/2.00  
% 11.80/2.00  fof(f6,axiom,(
% 11.80/2.00    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f58,plain,(
% 11.80/2.00    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f6])).
% 11.80/2.00  
% 11.80/2.00  fof(f81,plain,(
% 11.80/2.00    ( ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f1,axiom,(
% 11.80/2.00    v1_xboole_0(k1_xboole_0)),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f51,plain,(
% 11.80/2.00    v1_xboole_0(k1_xboole_0)),
% 11.80/2.00    inference(cnf_transformation,[],[f1])).
% 11.80/2.00  
% 11.80/2.00  fof(f2,axiom,(
% 11.80/2.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f52,plain,(
% 11.80/2.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f2])).
% 11.80/2.00  
% 11.80/2.00  fof(f86,plain,(
% 11.80/2.00    ( ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f9,axiom,(
% 11.80/2.00    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f24,plain,(
% 11.80/2.00    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(ennf_transformation,[],[f9])).
% 11.80/2.00  
% 11.80/2.00  fof(f68,plain,(
% 11.80/2.00    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f24])).
% 11.80/2.00  
% 11.80/2.00  fof(f8,axiom,(
% 11.80/2.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f22,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(ennf_transformation,[],[f8])).
% 11.80/2.00  
% 11.80/2.00  fof(f23,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f22])).
% 11.80/2.00  
% 11.80/2.00  fof(f37,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(nnf_transformation,[],[f23])).
% 11.80/2.00  
% 11.80/2.00  fof(f38,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f37])).
% 11.80/2.00  
% 11.80/2.00  fof(f39,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(rectify,[],[f38])).
% 11.80/2.00  
% 11.80/2.00  fof(f40,plain,(
% 11.80/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 11.80/2.00    introduced(choice_axiom,[])).
% 11.80/2.00  
% 11.80/2.00  fof(f41,plain,(
% 11.80/2.00    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.80/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 11.80/2.00  
% 11.80/2.00  fof(f63,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f41])).
% 11.80/2.00  
% 11.80/2.00  fof(f91,plain,(
% 11.80/2.00    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(equality_resolution,[],[f63])).
% 11.80/2.00  
% 11.80/2.00  fof(f10,axiom,(
% 11.80/2.00    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 11.80/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.80/2.00  
% 11.80/2.00  fof(f25,plain,(
% 11.80/2.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 11.80/2.00    inference(ennf_transformation,[],[f10])).
% 11.80/2.00  
% 11.80/2.00  fof(f26,plain,(
% 11.80/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 11.80/2.00    inference(flattening,[],[f25])).
% 11.80/2.00  
% 11.80/2.00  fof(f69,plain,(
% 11.80/2.00    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f26])).
% 11.80/2.00  
% 11.80/2.00  fof(f77,plain,(
% 11.80/2.00    v4_orders_2(sK2)),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f62,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f36])).
% 11.80/2.00  
% 11.80/2.00  fof(f64,plain,(
% 11.80/2.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(cnf_transformation,[],[f41])).
% 11.80/2.00  
% 11.80/2.00  fof(f90,plain,(
% 11.80/2.00    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.00    inference(equality_resolution,[],[f64])).
% 11.80/2.00  
% 11.80/2.00  fof(f80,plain,(
% 11.80/2.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f85,plain,(
% 11.80/2.00    ( ! [X5] : (k2_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f55,plain,(
% 11.80/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f32])).
% 11.80/2.00  
% 11.80/2.00  fof(f83,plain,(
% 11.80/2.00    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f84,plain,(
% 11.80/2.00    ( ! [X5] : (r2_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.80/2.00    inference(cnf_transformation,[],[f50])).
% 11.80/2.00  
% 11.80/2.00  fof(f60,plain,(
% 11.80/2.00    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.80/2.01    inference(cnf_transformation,[],[f36])).
% 11.80/2.01  
% 11.80/2.01  fof(f89,plain,(
% 11.80/2.01    ~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 11.80/2.01    inference(cnf_transformation,[],[f50])).
% 11.80/2.01  
% 11.80/2.01  cnf(c_3331,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,X2)
% 11.80/2.01      | r1_orders_2(X3,X4,X5)
% 11.80/2.01      | X3 != X0
% 11.80/2.01      | X4 != X1
% 11.80/2.01      | X5 != X2 ),
% 11.80/2.01      theory(equality) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4492,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,X2)
% 11.80/2.01      | r1_orders_2(sK2,sK5,X3)
% 11.80/2.01      | X3 != X2
% 11.80/2.01      | sK5 != X1
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_3331]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5120,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,sK5,X1)
% 11.80/2.01      | r1_orders_2(sK2,sK5,X2)
% 11.80/2.01      | X2 != X1
% 11.80/2.01      | sK5 != sK5
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4492]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6352,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0)
% 11.80/2.01      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X1))
% 11.80/2.01      | X0 != k2_yellow_0(sK2,X1)
% 11.80/2.01      | sK5 != sK5
% 11.80/2.01      | sK2 != sK2 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_5120]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_35429,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 11.80/2.01      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 11.80/2.01      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | sK5 != sK5
% 11.80/2.01      | sK2 != sK2 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_6352]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_25,plain,
% 11.80/2.01      ( ~ r1_lattice3(X0,X1,X2)
% 11.80/2.01      | r1_lattice3(X0,X3,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ r1_tarski(X3,X1)
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_37,negated_conjecture,
% 11.80/2.01      ( l1_orders_2(sK2) ),
% 11.80/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_807,plain,
% 11.80/2.01      ( ~ r1_lattice3(X0,X1,X2)
% 11.80/2.01      | r1_lattice3(X0,X3,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ r1_tarski(X3,X1)
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_808,plain,
% 11.80/2.01      ( ~ r1_lattice3(sK2,X0,X1)
% 11.80/2.01      | r1_lattice3(sK2,X2,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | ~ r1_tarski(X2,X0) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_807]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4374,plain,
% 11.80/2.01      ( ~ r1_lattice3(sK2,X0,sK5)
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 11.80/2.01      | ~ r1_tarski(X1,X0) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_808]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_11389,plain,
% 11.80/2.01      ( ~ r1_lattice3(sK2,X0,sK5)
% 11.80/2.01      | r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 11.80/2.01      | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),X0) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4374]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_24555,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.80/2.01      | ~ r1_lattice3(sK2,sK3,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 11.80/2.01      | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_11389]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_9,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1041,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_9,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1042,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_1041]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4140,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 11.80/2.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_1042]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_27,negated_conjecture,
% 11.80/2.01      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 11.80/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4166,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_28,negated_conjecture,
% 11.80/2.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4165,plain,
% 11.80/2.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4153,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X2,X1) = iProver_top
% 11.80/2.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r1_tarski(X2,X0) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5517,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) = iProver_top
% 11.80/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4165,c_4153]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5569,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 11.80/2.01      | r1_tarski(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4166,c_5517]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_36,negated_conjecture,
% 11.80/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.80/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4160,plain,
% 11.80/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6,plain,
% 11.80/2.01      ( m1_subset_1(X0,X1)
% 11.80/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.80/2.01      | ~ r2_hidden(X0,X2) ),
% 11.80/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4168,plain,
% 11.80/2.01      ( m1_subset_1(X0,X1) = iProver_top
% 11.80/2.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.80/2.01      | r2_hidden(X0,X2) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5061,plain,
% 11.80/2.01      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4160,c_4168]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_11,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,X3,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ r2_hidden(X2,X3)
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1005,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,X3,X1)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ r2_hidden(X2,X3)
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_11,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1006,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,X1)
% 11.80/2.01      | ~ r1_lattice3(sK2,X2,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | ~ r2_hidden(X1,X2) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_1005]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4142,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X2,X0) != iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r2_hidden(X1,X2) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6030,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) != iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r2_hidden(X0,X1) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4165,c_4142]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6050,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) != iProver_top
% 11.80/2.01      | r2_hidden(X0,X1) != iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_5061,c_6030]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_7217,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top
% 11.80/2.01      | r2_hidden(X0,sK4) != iProver_top
% 11.80/2.01      | r1_tarski(X1,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_5569,c_6050]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_61,plain,
% 11.80/2.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4,plain,
% 11.80/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.80/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4255,plain,
% 11.80/2.01      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.80/2.01      | ~ r1_tarski(k1_tarski(X0),sK3) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4256,plain,
% 11.80/2.01      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) = iProver_top
% 11.80/2.01      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_4255]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_23,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_839,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_23,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_840,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,X1)
% 11.80/2.01      | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_839]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4300,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0)
% 11.80/2.01      | ~ r1_lattice3(sK2,k1_tarski(X0),sK5)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_840]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4301,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_4300]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_2,plain,
% 11.80/2.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 11.80/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4544,plain,
% 11.80/2.01      ( ~ r2_hidden(X0,sK3) | r1_tarski(k1_tarski(X0),sK3) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_2]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4545,plain,
% 11.80/2.01      ( r2_hidden(X0,sK3) != iProver_top
% 11.80/2.01      | r1_tarski(k1_tarski(X0),sK3) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_4544]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4172,plain,
% 11.80/2.01      ( r2_hidden(X0,X1) != iProver_top
% 11.80/2.01      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4170,plain,
% 11.80/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.80/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_7,plain,
% 11.80/2.01      ( v1_finset_1(k1_tarski(X0)) ),
% 11.80/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_34,negated_conjecture,
% 11.80/2.01      ( r2_yellow_0(sK2,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.80/2.01      | ~ v1_finset_1(X0)
% 11.80/2.01      | k1_xboole_0 = X0 ),
% 11.80/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_589,plain,
% 11.80/2.01      ( r2_yellow_0(sK2,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.80/2.01      | k1_tarski(X1) != X0
% 11.80/2.01      | k1_xboole_0 = X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_590,plain,
% 11.80/2.01      ( r2_yellow_0(sK2,k1_tarski(X0))
% 11.80/2.01      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.80/2.01      | k1_xboole_0 = k1_tarski(X0) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_589]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4157,plain,
% 11.80/2.01      ( k1_xboole_0 = k1_tarski(X0)
% 11.80/2.01      | r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 11.80/2.01      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5386,plain,
% 11.80/2.01      ( k1_tarski(X0) = k1_xboole_0
% 11.80/2.01      | r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 11.80/2.01      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4170,c_4157]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_0,plain,
% 11.80/2.01      ( v1_xboole_0(k1_xboole_0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1,plain,
% 11.80/2.01      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 11.80/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_525,plain,
% 11.80/2.01      ( k1_tarski(X0) != k1_xboole_0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5391,plain,
% 11.80/2.01      ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 11.80/2.01      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_5386,c_525]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5397,plain,
% 11.80/2.01      ( r2_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4172,c_5391]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_7218,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4166,c_6050]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_29,negated_conjecture,
% 11.80/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.80/2.01      | r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 11.80/2.01      | ~ v1_finset_1(X0)
% 11.80/2.01      | k1_xboole_0 = X0 ),
% 11.80/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_604,plain,
% 11.80/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.80/2.01      | r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 11.80/2.01      | k1_tarski(X1) != X0
% 11.80/2.01      | k1_xboole_0 = X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_605,plain,
% 11.80/2.01      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.80/2.01      | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
% 11.80/2.01      | k1_xboole_0 = k1_tarski(X0) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_604]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4156,plain,
% 11.80/2.01      ( k1_xboole_0 = k1_tarski(X0)
% 11.80/2.01      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
% 11.80/2.01      | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_17,plain,
% 11.80/2.01      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_911,plain,
% 11.80/2.01      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_912,plain,
% 11.80/2.01      ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_911]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4147,plain,
% 11.80/2.01      ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6052,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) != iProver_top
% 11.80/2.01      | r2_hidden(k2_yellow_0(sK2,X0),X1) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4147,c_6030]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6335,plain,
% 11.80/2.01      ( k1_tarski(X0) = k1_xboole_0
% 11.80/2.01      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0))) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 11.80/2.01      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4156,c_6052]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_18793,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0))) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 11.80/2.01      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_6335,c_525]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_16,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 11.80/2.01      | ~ r2_yellow_0(X0,X1)
% 11.80/2.01      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_233,plain,
% 11.80/2.01      ( ~ r2_yellow_0(X0,X1)
% 11.80/2.01      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_16,c_17]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_234,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 11.80/2.01      | ~ r2_yellow_0(X0,X1)
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(renaming,[status(thm)],[c_233]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_795,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 11.80/2.01      | ~ r2_yellow_0(X0,X1)
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_234,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_796,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) | ~ r2_yellow_0(sK2,X0) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_795]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4154,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
% 11.80/2.01      | r2_yellow_0(sK2,X0) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_19,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,X3,X2)
% 11.80/2.01      | r1_lattice3(X0,X3,X1)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ v4_orders_2(X0)
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_38,negated_conjecture,
% 11.80/2.01      ( v4_orders_2(sK2) ),
% 11.80/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_531,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,X2)
% 11.80/2.01      | ~ r1_lattice3(X0,X3,X2)
% 11.80/2.01      | r1_lattice3(X0,X3,X1)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0)
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_532,plain,
% 11.80/2.01      ( ~ r1_orders_2(sK2,X0,X1)
% 11.80/2.01      | ~ r1_lattice3(sK2,X2,X1)
% 11.80/2.01      | r1_lattice3(sK2,X2,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | ~ l1_orders_2(sK2) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_531]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_534,plain,
% 11.80/2.01      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | r1_lattice3(sK2,X2,X0)
% 11.80/2.01      | ~ r1_lattice3(sK2,X2,X1)
% 11.80/2.01      | ~ r1_orders_2(sK2,X0,X1) ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_532,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_535,plain,
% 11.80/2.01      ( ~ r1_orders_2(sK2,X0,X1)
% 11.80/2.01      | ~ r1_lattice3(sK2,X2,X1)
% 11.80/2.01      | r1_lattice3(sK2,X2,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(renaming,[status(thm)],[c_534]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4159,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X2,X1) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X2,X0) = iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6235,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,X0) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) = iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4165,c_4159]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6278,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,sK5) = iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4147,c_6235]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6673,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0)) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X0,sK5) = iProver_top
% 11.80/2.01      | r2_yellow_0(sK2,X0) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4154,c_6278]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_18821,plain,
% 11.80/2.01      ( r1_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 11.80/2.01      | r2_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 11.80/2.01      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_18793,c_6673]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_19989,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK3) != iProver_top ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_7217,c_61,c_4256,c_4301,c_4545,c_5061,c_5397,c_7218,
% 11.80/2.01                 c_18821]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_8,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 11.80/2.01      | r1_lattice3(X0,X2,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1056,plain,
% 11.80/2.01      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 11.80/2.01      | r1_lattice3(X0,X2,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_8,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1057,plain,
% 11.80/2.01      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 11.80/2.01      | r1_lattice3(sK2,X1,X0)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_1056]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4139,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,sK0(sK2,X1,X0)) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,X1,X0) = iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_20003,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 11.80/2.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_19989,c_4139]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_20213,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 11.80/2.01      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
% 11.80/2.01      inference(global_propositional_subsumption,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_20003,c_61]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_20219,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 11.80/2.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4140,c_20213]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_20220,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK3,sK5) | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_20219]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_3330,plain,
% 11.80/2.01      ( X0 != X1 | sK0(X0,X2,X3) = sK0(X1,X2,X3) ),
% 11.80/2.01      theory(equality) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_13283,plain,
% 11.80/2.01      ( sK0(sK2,sK4,sK5) = sK0(X0,sK4,sK5) | sK2 != X0 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_3330]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_13284,plain,
% 11.80/2.01      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) | sK2 != sK2 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_13283]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_15,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 11.80/2.01      | ~ r1_lattice3(X0,X2,X1)
% 11.80/2.01      | ~ r2_yellow_0(X0,X2)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f90]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_920,plain,
% 11.80/2.01      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 11.80/2.01      | ~ r1_lattice3(X0,X2,X1)
% 11.80/2.01      | ~ r2_yellow_0(X0,X2)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.80/2.01      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_921,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
% 11.80/2.01      | ~ r1_lattice3(sK2,X1,X0)
% 11.80/2.01      | ~ r2_yellow_0(sK2,X1)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_920]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_930,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
% 11.80/2.01      | ~ r1_lattice3(sK2,X1,X0)
% 11.80/2.01      | ~ r2_yellow_0(sK2,X1)
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(forward_subsumption_resolution,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_921,c_912]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6807,plain,
% 11.80/2.01      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 11.80/2.01      | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 11.80/2.01      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_930]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_8111,plain,
% 11.80/2.01      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 11.80/2.01      | ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.80/2.01      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_6807]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_3324,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5582,plain,
% 11.80/2.01      ( X0 != X1 | X0 = k2_yellow_0(sK2,X2) | k2_yellow_0(sK2,X2) != X1 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_3324]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6758,plain,
% 11.80/2.01      ( X0 != sK0(sK2,sK4,sK5)
% 11.80/2.01      | X0 = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_5582]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_7944,plain,
% 11.80/2.01      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 11.80/2.01      | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_6758]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_35,negated_conjecture,
% 11.80/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.80/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4161,plain,
% 11.80/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5060,plain,
% 11.80/2.01      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 11.80/2.01      | r2_hidden(X0,sK4) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4161,c_4168]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_30,negated_conjecture,
% 11.80/2.01      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ r2_hidden(X0,sK4)
% 11.80/2.01      | k2_yellow_0(sK2,sK6(X0)) = X0 ),
% 11.80/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4164,plain,
% 11.80/2.01      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 11.80/2.01      | r2_hidden(X0,sK4) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5142,plain,
% 11.80/2.01      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 11.80/2.01      | r2_hidden(X0,sK4) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_5060,c_4164]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5351,plain,
% 11.80/2.01      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 11.80/2.01      | r1_lattice3(sK2,sK4,X0) = iProver_top
% 11.80/2.01      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4140,c_5142]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6832,plain,
% 11.80/2.01      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.80/2.01      inference(superposition,[status(thm)],[c_4165,c_5351]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5,plain,
% 11.80/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.80/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_6763,plain,
% 11.80/2.01      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 11.80/2.01      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_3323,plain,( X0 = X0 ),theory(equality) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5561,plain,
% 11.80/2.01      ( sK5 = sK5 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_3323]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_32,negated_conjecture,
% 11.80/2.01      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
% 11.80/2.01      | ~ r2_hidden(X0,sK4) ),
% 11.80/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5303,plain,
% 11.80/2.01      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.80/2.01      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 11.80/2.01      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_32]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_31,negated_conjecture,
% 11.80/2.01      ( r2_yellow_0(sK2,sK6(X0))
% 11.80/2.01      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.80/2.01      | ~ r2_hidden(X0,sK4) ),
% 11.80/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_5304,plain,
% 11.80/2.01      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.80/2.01      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.80/2.01      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_31]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4348,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 11.80/2.01      | r2_hidden(sK0(sK2,X0,sK5),X0) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_1042]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4508,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK4,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 11.80/2.01      | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4348]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4360,plain,
% 11.80/2.01      ( ~ r1_orders_2(sK2,sK5,sK0(sK2,X0,sK5))
% 11.80/2.01      | r1_lattice3(sK2,X0,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_1057]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4473,plain,
% 11.80/2.01      ( ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5)
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4360]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_10,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.80/2.01      | ~ l1_orders_2(X0) ),
% 11.80/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1026,plain,
% 11.80/2.01      ( r1_lattice3(X0,X1,X2)
% 11.80/2.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.80/2.01      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.80/2.01      | sK2 != X0 ),
% 11.80/2.01      inference(resolution_lifted,[status(thm)],[c_10,c_37]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_1027,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,X1)
% 11.80/2.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.80/2.01      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.80/2.01      inference(unflattening,[status(thm)],[c_1026]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4280,plain,
% 11.80/2.01      ( r1_lattice3(sK2,X0,sK5)
% 11.80/2.01      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_1027]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_4470,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK4,sK5)
% 11.80/2.01      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.80/2.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_4280]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_3350,plain,
% 11.80/2.01      ( sK2 = sK2 ),
% 11.80/2.01      inference(instantiation,[status(thm)],[c_3323]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_26,negated_conjecture,
% 11.80/2.01      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 11.80/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(c_63,plain,
% 11.80/2.01      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 11.80/2.01      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 11.80/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.80/2.01  
% 11.80/2.01  cnf(contradiction,plain,
% 11.80/2.01      ( $false ),
% 11.80/2.01      inference(minisat,
% 11.80/2.01                [status(thm)],
% 11.80/2.01                [c_35429,c_24555,c_20220,c_20219,c_13284,c_8111,c_7944,
% 11.80/2.01                 c_6832,c_6763,c_5561,c_5303,c_5304,c_4508,c_4473,c_4470,
% 11.80/2.01                 c_3350,c_63,c_26,c_61,c_28]) ).
% 11.80/2.01  
% 11.80/2.01  
% 11.80/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.80/2.01  
% 11.80/2.01  ------                               Statistics
% 11.80/2.01  
% 11.80/2.01  ------ General
% 11.80/2.01  
% 11.80/2.01  abstr_ref_over_cycles:                  0
% 11.80/2.01  abstr_ref_under_cycles:                 0
% 11.80/2.01  gc_basic_clause_elim:                   0
% 11.80/2.01  forced_gc_time:                         0
% 11.80/2.01  parsing_time:                           0.007
% 11.80/2.01  unif_index_cands_time:                  0.
% 11.80/2.01  unif_index_add_time:                    0.
% 11.80/2.01  orderings_time:                         0.
% 11.80/2.01  out_proof_time:                         0.015
% 11.80/2.01  total_time:                             1.244
% 11.80/2.01  num_of_symbols:                         54
% 11.80/2.01  num_of_terms:                           24506
% 11.80/2.01  
% 11.80/2.01  ------ Preprocessing
% 11.80/2.01  
% 11.80/2.01  num_of_splits:                          0
% 11.80/2.01  num_of_split_atoms:                     0
% 11.80/2.01  num_of_reused_defs:                     0
% 11.80/2.01  num_eq_ax_congr_red:                    28
% 11.80/2.01  num_of_sem_filtered_clauses:            1
% 11.80/2.01  num_of_subtypes:                        0
% 11.80/2.01  monotx_restored_types:                  0
% 11.80/2.01  sat_num_of_epr_types:                   0
% 11.80/2.01  sat_num_of_non_cyclic_types:            0
% 11.80/2.01  sat_guarded_non_collapsed_types:        0
% 11.80/2.01  num_pure_diseq_elim:                    0
% 11.80/2.01  simp_replaced_by:                       0
% 11.80/2.01  res_preprocessed:                       173
% 11.80/2.01  prep_upred:                             0
% 11.80/2.01  prep_unflattend:                        136
% 11.80/2.01  smt_new_axioms:                         0
% 11.80/2.01  pred_elim_cands:                        7
% 11.80/2.01  pred_elim:                              4
% 11.80/2.01  pred_elim_cl:                           4
% 11.80/2.01  pred_elim_cycles:                       11
% 11.80/2.01  merged_defs:                            24
% 11.80/2.01  merged_defs_ncl:                        0
% 11.80/2.01  bin_hyper_res:                          24
% 11.80/2.01  prep_cycles:                            4
% 11.80/2.01  pred_elim_time:                         0.029
% 11.80/2.01  splitting_time:                         0.
% 11.80/2.01  sem_filter_time:                        0.
% 11.80/2.01  monotx_time:                            0.
% 11.80/2.01  subtype_inf_time:                       0.
% 11.80/2.01  
% 11.80/2.01  ------ Problem properties
% 11.80/2.01  
% 11.80/2.01  clauses:                                35
% 11.80/2.01  conjectures:                            8
% 11.80/2.01  epr:                                    2
% 11.80/2.01  horn:                                   27
% 11.80/2.01  ground:                                 5
% 11.80/2.01  unary:                                  5
% 11.80/2.01  binary:                                 7
% 11.80/2.01  lits:                                   108
% 11.80/2.01  lits_eq:                                8
% 11.80/2.01  fd_pure:                                0
% 11.80/2.01  fd_pseudo:                              0
% 11.80/2.01  fd_cond:                                0
% 11.80/2.01  fd_pseudo_cond:                         3
% 11.80/2.01  ac_symbols:                             0
% 11.80/2.01  
% 11.80/2.01  ------ Propositional Solver
% 11.80/2.01  
% 11.80/2.01  prop_solver_calls:                      33
% 11.80/2.01  prop_fast_solver_calls:                 4769
% 11.80/2.01  smt_solver_calls:                       0
% 11.80/2.01  smt_fast_solver_calls:                  0
% 11.80/2.01  prop_num_of_clauses:                    16776
% 11.80/2.01  prop_preprocess_simplified:             25602
% 11.80/2.01  prop_fo_subsumed:                       319
% 11.80/2.01  prop_solver_time:                       0.
% 11.80/2.01  smt_solver_time:                        0.
% 11.80/2.01  smt_fast_solver_time:                   0.
% 11.80/2.01  prop_fast_solver_time:                  0.
% 11.80/2.01  prop_unsat_core_time:                   0.001
% 11.80/2.01  
% 11.80/2.01  ------ QBF
% 11.80/2.01  
% 11.80/2.01  qbf_q_res:                              0
% 11.80/2.01  qbf_num_tautologies:                    0
% 11.80/2.01  qbf_prep_cycles:                        0
% 11.80/2.01  
% 11.80/2.01  ------ BMC1
% 11.80/2.01  
% 11.80/2.01  bmc1_current_bound:                     -1
% 11.80/2.01  bmc1_last_solved_bound:                 -1
% 11.80/2.01  bmc1_unsat_core_size:                   -1
% 11.80/2.01  bmc1_unsat_core_parents_size:           -1
% 11.80/2.01  bmc1_merge_next_fun:                    0
% 11.80/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.80/2.01  
% 11.80/2.01  ------ Instantiation
% 11.80/2.01  
% 11.80/2.01  inst_num_of_clauses:                    3533
% 11.80/2.01  inst_num_in_passive:                    651
% 11.80/2.01  inst_num_in_active:                     1548
% 11.80/2.01  inst_num_in_unprocessed:                1333
% 11.80/2.01  inst_num_of_loops:                      2193
% 11.80/2.01  inst_num_of_learning_restarts:          0
% 11.80/2.01  inst_num_moves_active_passive:          639
% 11.80/2.01  inst_lit_activity:                      0
% 11.80/2.01  inst_lit_activity_moves:                1
% 11.80/2.01  inst_num_tautologies:                   0
% 11.80/2.01  inst_num_prop_implied:                  0
% 11.80/2.01  inst_num_existing_simplified:           0
% 11.80/2.01  inst_num_eq_res_simplified:             0
% 11.80/2.01  inst_num_child_elim:                    0
% 11.80/2.01  inst_num_of_dismatching_blockings:      1750
% 11.80/2.01  inst_num_of_non_proper_insts:           5219
% 11.80/2.01  inst_num_of_duplicates:                 0
% 11.80/2.01  inst_inst_num_from_inst_to_res:         0
% 11.80/2.01  inst_dismatching_checking_time:         0.
% 11.80/2.01  
% 11.80/2.01  ------ Resolution
% 11.80/2.01  
% 11.80/2.01  res_num_of_clauses:                     0
% 11.80/2.01  res_num_in_passive:                     0
% 11.80/2.01  res_num_in_active:                      0
% 11.80/2.01  res_num_of_loops:                       177
% 11.80/2.01  res_forward_subset_subsumed:            116
% 11.80/2.01  res_backward_subset_subsumed:           0
% 11.80/2.01  res_forward_subsumed:                   1
% 11.80/2.01  res_backward_subsumed:                  0
% 11.80/2.01  res_forward_subsumption_resolution:     6
% 11.80/2.01  res_backward_subsumption_resolution:    0
% 11.80/2.01  res_clause_to_clause_subsumption:       8908
% 11.80/2.01  res_orphan_elimination:                 0
% 11.80/2.01  res_tautology_del:                      334
% 11.80/2.01  res_num_eq_res_simplified:              0
% 11.80/2.01  res_num_sel_changes:                    0
% 11.80/2.01  res_moves_from_active_to_pass:          0
% 11.80/2.01  
% 11.80/2.01  ------ Superposition
% 11.80/2.01  
% 11.80/2.01  sup_time_total:                         0.
% 11.80/2.01  sup_time_generating:                    0.
% 11.80/2.01  sup_time_sim_full:                      0.
% 11.80/2.01  sup_time_sim_immed:                     0.
% 11.80/2.01  
% 11.80/2.01  sup_num_of_clauses:                     1386
% 11.80/2.01  sup_num_in_active:                      332
% 11.80/2.01  sup_num_in_passive:                     1054
% 11.80/2.01  sup_num_of_loops:                       438
% 11.80/2.01  sup_fw_superposition:                   1507
% 11.80/2.01  sup_bw_superposition:                   1733
% 11.80/2.01  sup_immediate_simplified:               1257
% 11.80/2.01  sup_given_eliminated:                   13
% 11.80/2.01  comparisons_done:                       0
% 11.80/2.01  comparisons_avoided:                    35
% 11.80/2.01  
% 11.80/2.01  ------ Simplifications
% 11.80/2.01  
% 11.80/2.01  
% 11.80/2.01  sim_fw_subset_subsumed:                 266
% 11.80/2.01  sim_bw_subset_subsumed:                 222
% 11.80/2.01  sim_fw_subsumed:                        721
% 11.80/2.01  sim_bw_subsumed:                        329
% 11.80/2.01  sim_fw_subsumption_res:                 0
% 11.80/2.01  sim_bw_subsumption_res:                 0
% 11.80/2.01  sim_tautology_del:                      31
% 11.80/2.01  sim_eq_tautology_del:                   6
% 11.80/2.01  sim_eq_res_simp:                        2
% 11.80/2.01  sim_fw_demodulated:                     40
% 11.80/2.01  sim_bw_demodulated:                     0
% 11.80/2.01  sim_light_normalised:                   32
% 11.80/2.01  sim_joinable_taut:                      0
% 11.80/2.01  sim_joinable_simp:                      0
% 11.80/2.01  sim_ac_normalised:                      0
% 11.80/2.01  sim_smt_subsumption:                    0
% 11.80/2.01  
%------------------------------------------------------------------------------
