%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1672+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:09 EST 2020

% Result     : Theorem 35.34s
% Output     : CNFRefutation 35.34s
% Verified   : 
% Statistics : Number of formulae       :  264 (4645 expanded)
%              Number of clauses        :  183 ( 974 expanded)
%              Number of leaves         :   25 (1280 expanded)
%              Depth                    :   35
%              Number of atoms          : 1301 (76889 expanded)
%              Number of equality atoms :  285 (10548 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).

fof(f77,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f81,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_532,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_37])).

cnf(c_533,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X2)
    | r1_orders_2(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X1,X2)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_36])).

cnf(c_536,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X0)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_71248,plain,
    ( ~ r1_orders_2(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),X0)
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_73097,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_yellow_0(sK2,X0))
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
    | ~ m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_71248])).

cnf(c_111262,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_73097])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_970,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_36])).

cnf(c_971,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_86339,plain,
    ( r1_orders_2(sK2,sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),X1)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X1)
    | ~ r2_hidden(sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_95571,plain,
    ( r1_orders_2(sK2,sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r2_hidden(sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(X0,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_86339])).

cnf(c_95573,plain,
    ( r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r2_hidden(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_95571])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3039,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1006,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_36])).

cnf(c_1007,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_3014,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_13,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3046,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3044,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_580,plain,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_581,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_3030,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3038,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_54,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3035,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3042,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3477,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_3042])).

cnf(c_3598,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3038,c_54,c_3477])).

cnf(c_3599,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3598])).

cnf(c_5118,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0)))) = k1_yellow_0(sK2,k1_tarski(X0))
    | k1_tarski(X0) = k1_xboole_0
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3599])).

cnf(c_12835,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0)))) = k1_yellow_0(sK2,k1_tarski(X0))
    | k1_tarski(X0) = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3044,c_5118])).

cnf(c_13098,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(X0)))) = k1_yellow_0(sK2,k1_tarski(X0))
    | k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_12835])).

cnf(c_13103,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0)))
    | k1_tarski(sK0(sK2,sK3,X0)) = k1_xboole_0
    | r2_lattice3(sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_13098])).

cnf(c_29507,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3039,c_13103])).

cnf(c_25,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_862,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_863,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_23,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_810,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_811,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_26,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3758,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_811,c_26])).

cnf(c_3767,plain,
    ( ~ r1_tarski(X0,sK3)
    | r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_27])).

cnf(c_3768,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r1_tarski(X0,sK3) ),
    inference(renaming,[status(thm)],[c_3767])).

cnf(c_4772,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r1_tarski(k1_tarski(X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_863,c_3768])).

cnf(c_8367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r1_tarski(k1_tarski(X0),sK3)
    | r2_lattice3(sK2,sK4,sK5)
    | r1_orders_2(sK2,X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4772,c_27])).

cnf(c_8368,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r1_tarski(k1_tarski(X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_8367])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1021,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_36])).

cnf(c_1022,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_8397,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ r1_tarski(k1_tarski(sK0(sK2,X0,sK5)),sK3)
    | ~ m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_8368,c_1022])).

cnf(c_2146,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2173,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_3166,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | r2_hidden(sK0(sK2,X0,sK5),X0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_3353,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_3367,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_2,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_991,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_36])).

cnf(c_992,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_3156,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_3562,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_30,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3583,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3582,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3916,plain,
    ( r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_9,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_9])).

cnf(c_244,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_764,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_36])).

cnf(c_765,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_3931,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
    | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_4484,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3931])).

cnf(c_2149,plain,
    ( X0 != X1
    | sK0(X0,X2,X3) = sK0(X1,X2,X3) ),
    theory(equality)).

cnf(c_4945,plain,
    ( X0 != sK2
    | sK0(X0,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_4948,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4945])).

cnf(c_2147,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3810,plain,
    ( X0 != X1
    | X0 = k1_yellow_0(sK2,X2)
    | k1_yellow_0(sK2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_5287,plain,
    ( X0 != sK0(sK2,sK4,sK5)
    | X0 = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3810])).

cnf(c_5929,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5287])).

cnf(c_4382,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ r2_lattice3(sK2,sK3,X0)
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_6364,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4382])).

cnf(c_6401,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_3604,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r2_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_3599])).

cnf(c_7916,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3039,c_3604])).

cnf(c_7922,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7916])).

cnf(c_2150,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4117,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,X3),sK5)
    | X1 != k1_yellow_0(sK2,X3)
    | X2 != sK5
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_5408,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X1 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | X2 != sK5
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_4117])).

cnf(c_6847,plain,
    ( r1_orders_2(X0,X1,sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X1 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | X0 != sK2
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5408])).

cnf(c_15669,plain,
    ( r1_orders_2(X0,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X0 != sK2
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6847])).

cnf(c_15671,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_15669])).

cnf(c_15715,plain,
    ( r2_lattice3(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8397,c_27,c_26,c_2173,c_3353,c_3367,c_3562,c_3583,c_3582,c_3916,c_4484,c_4948,c_5929,c_6364,c_6401,c_7922,c_15671])).

cnf(c_29514,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29507])).

cnf(c_29534,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29507,c_27,c_26,c_25,c_2173,c_3353,c_3367,c_3562,c_3583,c_3582,c_3916,c_4484,c_4948,c_5929,c_6364,c_6401,c_7922,c_15671,c_29514])).

cnf(c_29535,plain,
    ( k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_29534])).

cnf(c_898,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_36])).

cnf(c_899,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_3020,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_3040,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3025,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_5362,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3039,c_3025])).

cnf(c_5586,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3040,c_5362])).

cnf(c_5595,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5586,c_5362])).

cnf(c_3022,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_5807,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_3022])).

cnf(c_60,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3043,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3229,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_3043])).

cnf(c_5816,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_5362])).

cnf(c_15435,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_5816])).

cnf(c_15717,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15715])).

cnf(c_15775,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15435,c_15717])).

cnf(c_15788,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15775,c_5362])).

cnf(c_15975,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15788,c_3022])).

cnf(c_18337,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5807,c_60,c_15975])).

cnf(c_18338,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18337])).

cnf(c_18344,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5) = iProver_top
    | r1_tarski(k1_tarski(k1_yellow_0(sK2,X0)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_18338])).

cnf(c_87489,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_18344])).

cnf(c_87496,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29535,c_87489])).

cnf(c_3540,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_521,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_3033,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_4679,plain,
    ( r2_lattice3(sK2,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_3033])).

cnf(c_11437,plain,
    ( r2_lattice3(sK2,k1_xboole_0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3039,c_4679])).

cnf(c_11444,plain,
    ( r2_lattice3(sK2,k1_xboole_0,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11437])).

cnf(c_3357,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | ~ r2_lattice3(sK2,k1_tarski(X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_21826,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3357])).

cnf(c_42495,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_2148,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_70908,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1
    | sK5 != X2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_71524,plain,
    ( ~ r2_lattice3(X0,X1,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_70908])).

cnf(c_74430,plain,
    ( ~ r2_lattice3(X0,k1_xboole_0,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_71524])).

cnf(c_74432,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ r2_lattice3(sK2,k1_xboole_0,sK5)
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_74430])).

cnf(c_87785,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,sK6(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87496,c_27,c_26,c_25,c_2173,c_3353,c_3367,c_3540,c_3562,c_3583,c_3582,c_3916,c_4484,c_4948,c_5929,c_6364,c_6401,c_7922,c_11444,c_15671,c_21826,c_42495,c_74432])).

cnf(c_87790,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29535,c_87785])).

cnf(c_87792,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_87790])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_236,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_9])).

cnf(c_237,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_782,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_36])).

cnf(c_783,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0))
    | ~ r1_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_81217,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_70388,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
    | r2_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_70917,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_70388])).

cnf(c_21287,plain,
    ( k1_tarski(X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_62280,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_21287])).

cnf(c_21291,plain,
    ( X0 != X1
    | k1_tarski(X2) != X1
    | k1_tarski(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_43440,plain,
    ( X0 != k1_tarski(X1)
    | k1_tarski(X1) = X0
    | k1_tarski(X1) != k1_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_21291])).

cnf(c_54647,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_43440])).

cnf(c_3356,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),sK5)
    | r2_hidden(sK0(sK2,k1_tarski(X0),sK5),k1_tarski(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_53677,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | r2_hidden(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_18128,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),sK5)
    | m1_subset_1(sK0(sK2,k1_tarski(X0),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_53678,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_18128])).

cnf(c_48926,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_33,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_565,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_566,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_48927,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_29544,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29535,c_3020])).

cnf(c_29576,plain,
    ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29544])).

cnf(c_21854,plain,
    ( ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3)
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_17742,plain,
    ( r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3)
    | ~ r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3453,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111262,c_95573,c_87792,c_81217,c_74432,c_70917,c_62280,c_54647,c_53677,c_53678,c_48926,c_48927,c_42495,c_29576,c_21854,c_21826,c_17742,c_15715,c_11444,c_3540,c_3453,c_3367,c_2173,c_25,c_27])).


%------------------------------------------------------------------------------
