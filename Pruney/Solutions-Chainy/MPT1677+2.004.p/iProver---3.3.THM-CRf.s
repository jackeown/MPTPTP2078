%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:10 EST 2020

% Result     : Theorem 35.85s
% Output     : CNFRefutation 35.85s
% Verified   : 
% Statistics : Number of formulae       :  249 (2446 expanded)
%              Number of clauses        :  176 ( 553 expanded)
%              Number of leaves         :   23 ( 707 expanded)
%              Depth                    :   29
%              Number of atoms          : 1273 (40430 expanded)
%              Number of equality atoms :  343 (5383 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f44,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
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
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).

fof(f79,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X7] :
      ( r2_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X5] :
      ( k2_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ! [X5] :
      ( r2_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_913,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_914,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_68278,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1),X0) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_83834,plain,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5))
    | ~ m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_68278])).

cnf(c_3189,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_58232,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | sK0(sK2,sK4,sK5) != X2
    | sK5 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3189])).

cnf(c_58572,plain,
    ( ~ r1_orders_2(X0,sK5,X1)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | sK0(sK2,sK4,sK5) != X1
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_58232])).

cnf(c_67049,plain,
    ( ~ r1_orders_2(X0,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_58572])).

cnf(c_67051,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_67049])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_58370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_59224,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK6(sK0(sK2,sK4,sK5)))
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_58370])).

cnf(c_59645,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK6(sK0(sK2,sK4,sK5)))
    | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK3) ),
    inference(instantiation,[status(thm)],[c_59224])).

cnf(c_64542,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK6(sK0(sK2,sK4,sK5)))
    | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_59645])).

cnf(c_11,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_932,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_933,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_932])).

cnf(c_58781,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_61588,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_58781])).

cnf(c_10,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_947,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_948,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_58780,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK6(sK0(sK2,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_60438,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK6(sK0(sK2,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_58780])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_962,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_963,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_58779,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | ~ r1_orders_2(sK2,X0,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_60408,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_58779])).

cnf(c_16,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_829,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_830,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_58293,plain,
    ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_59818,plain,
    ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_58293])).

cnf(c_3910,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3931,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3938,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4288,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3931,c_3938])).

cnf(c_3916,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_5283,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_3916])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3930,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4289,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3930,c_3938])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3935,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_762,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_763,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_3920,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_3912,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_4975,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X0,X2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_3912])).

cnf(c_6540,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_4975])).

cnf(c_6563,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_6540])).

cnf(c_7009,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4289,c_6563])).

cnf(c_7421,plain,
    ( r1_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tarski(k2_yellow_0(sK2,X0))) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5283,c_7009])).

cnf(c_63,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3936,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4974,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3936,c_3912])).

cnf(c_5039,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_63,c_4289])).

cnf(c_5046,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_3912])).

cnf(c_11110,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5046,c_63])).

cnf(c_11111,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_11110])).

cnf(c_11118,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_11111])).

cnf(c_17,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_814,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_815,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_3917,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_4699,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_3917])).

cnf(c_19,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_507,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,X3)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_508,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_lattice3(sK2,X0,X2)
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_35])).

cnf(c_511,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_3929,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK2,X0,X2) = iProver_top
    | r1_orders_2(sK2,X2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_5607,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4699,c_3929])).

cnf(c_11682,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_5607])).

cnf(c_11737,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11118,c_11682])).

cnf(c_47921,plain,
    ( r2_yellow_0(sK2,X0) != iProver_top
    | r1_orders_2(sK2,sK5,X1) = iProver_top
    | r2_hidden(X1,k1_tarski(k2_yellow_0(sK2,X0))) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7421,c_63,c_11737])).

cnf(c_47922,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_yellow_0(sK2,X1) != iProver_top
    | r2_hidden(X0,k1_tarski(k2_yellow_0(sK2,X1))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_47921])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_65,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4044,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_4185,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4044])).

cnf(c_4186,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4185])).

cnf(c_4094,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,X0,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_4184,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_4188,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4184])).

cnf(c_4087,plain,
    ( r1_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_4183,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_4087])).

cnf(c_4190,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4183])).

cnf(c_3,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4019,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4336,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_4337,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4336])).

cnf(c_23,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_744,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_745,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_4059,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0),sK5)
    | r1_orders_2(sK2,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_4543,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4059])).

cnf(c_4547,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4543])).

cnf(c_5,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,negated_conjecture,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_565,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_32])).

cnf(c_566,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_4621,plain,
    ( r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_4622,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4621])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_4620,plain,
    ( ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_4624,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_3184,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8049,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_3184])).

cnf(c_3185,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6670,plain,
    ( X0 != X1
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_3185])).

cnf(c_8101,plain,
    ( X0 != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_6670])).

cnf(c_12954,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_8101])).

cnf(c_4789,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15106,plain,
    ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_4789])).

cnf(c_15107,plain,
    ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15106])).

cnf(c_15109,plain,
    ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15107])).

cnf(c_15156,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_15157,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15156])).

cnf(c_4104,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_5584,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0)
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ r1_orders_2(sK2,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4104])).

cnf(c_18734,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5584])).

cnf(c_18741,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18734])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_501,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_23663,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_14260,plain,
    ( ~ r1_lattice3(sK2,X0,sK5)
    | r1_orders_2(sK2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_46021,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))))
    | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_14260])).

cnf(c_46022,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5)))) = iProver_top
    | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46021])).

cnf(c_46024,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
    | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46022])).

cnf(c_47927,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47922,c_44,c_63,c_65,c_4186,c_4188,c_4190,c_4337,c_4547,c_4622,c_4624,c_5039,c_8049,c_12954,c_15109,c_15157,c_18741,c_23663,c_46024])).

cnf(c_47928,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_47927])).

cnf(c_3909,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,sK0(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_47961,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_47928,c_3909])).

cnf(c_48834,plain,
    ( r1_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47961,c_63])).

cnf(c_48840,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3910,c_48834])).

cnf(c_48844,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_48840])).

cnf(c_3188,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4054,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,u1_struct_0(sK2))
    | X2 != X0
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_3188])).

cnf(c_4264,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X2,u1_struct_0(sK2))
    | X2 != X0
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4054])).

cnf(c_13917,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != X0
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_27474,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(X0))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_13917])).

cnf(c_27476,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_27474])).

cnf(c_8082,plain,
    ( X0 != X1
    | sK0(sK2,sK4,sK5) != X1
    | sK0(sK2,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3185])).

cnf(c_16594,plain,
    ( X0 != sK0(X1,sK4,sK5)
    | sK0(sK2,sK4,sK5) = X0
    | sK0(sK2,sK4,sK5) != sK0(X1,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_8082])).

cnf(c_20571,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_16594])).

cnf(c_8148,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3184])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | k2_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3934,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4451,plain,
    ( k2_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_3934])).

cnf(c_4981,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r1_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3910,c_4451])).

cnf(c_6012,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_4981])).

cnf(c_4432,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3184])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4421,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4422,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4145,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_4087])).

cnf(c_4142,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_4133,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4044])).

cnf(c_3209,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3184])).

cnf(c_3190,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3201,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83834,c_67051,c_64542,c_61588,c_60438,c_60408,c_59818,c_48844,c_48840,c_27476,c_20571,c_8148,c_6012,c_4432,c_4421,c_4422,c_4145,c_4142,c_4133,c_3209,c_3201,c_65,c_24,c_63,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.85/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.85/4.99  
% 35.85/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.85/4.99  
% 35.85/4.99  ------  iProver source info
% 35.85/4.99  
% 35.85/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.85/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.85/4.99  git: non_committed_changes: false
% 35.85/4.99  git: last_make_outside_of_git: false
% 35.85/4.99  
% 35.85/4.99  ------ 
% 35.85/4.99  
% 35.85/4.99  ------ Input Options
% 35.85/4.99  
% 35.85/4.99  --out_options                           all
% 35.85/4.99  --tptp_safe_out                         true
% 35.85/4.99  --problem_path                          ""
% 35.85/4.99  --include_path                          ""
% 35.85/4.99  --clausifier                            res/vclausify_rel
% 35.85/4.99  --clausifier_options                    ""
% 35.85/4.99  --stdin                                 false
% 35.85/4.99  --stats_out                             all
% 35.85/4.99  
% 35.85/4.99  ------ General Options
% 35.85/4.99  
% 35.85/4.99  --fof                                   false
% 35.85/4.99  --time_out_real                         305.
% 35.85/4.99  --time_out_virtual                      -1.
% 35.85/4.99  --symbol_type_check                     false
% 35.85/4.99  --clausify_out                          false
% 35.85/4.99  --sig_cnt_out                           false
% 35.85/4.99  --trig_cnt_out                          false
% 35.85/4.99  --trig_cnt_out_tolerance                1.
% 35.85/4.99  --trig_cnt_out_sk_spl                   false
% 35.85/4.99  --abstr_cl_out                          false
% 35.85/4.99  
% 35.85/4.99  ------ Global Options
% 35.85/4.99  
% 35.85/4.99  --schedule                              default
% 35.85/4.99  --add_important_lit                     false
% 35.85/4.99  --prop_solver_per_cl                    1000
% 35.85/4.99  --min_unsat_core                        false
% 35.85/4.99  --soft_assumptions                      false
% 35.85/4.99  --soft_lemma_size                       3
% 35.85/4.99  --prop_impl_unit_size                   0
% 35.85/4.99  --prop_impl_unit                        []
% 35.85/4.99  --share_sel_clauses                     true
% 35.85/4.99  --reset_solvers                         false
% 35.85/4.99  --bc_imp_inh                            [conj_cone]
% 35.85/4.99  --conj_cone_tolerance                   3.
% 35.85/4.99  --extra_neg_conj                        none
% 35.85/4.99  --large_theory_mode                     true
% 35.85/4.99  --prolific_symb_bound                   200
% 35.85/4.99  --lt_threshold                          2000
% 35.85/4.99  --clause_weak_htbl                      true
% 35.85/4.99  --gc_record_bc_elim                     false
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing Options
% 35.85/4.99  
% 35.85/4.99  --preprocessing_flag                    true
% 35.85/4.99  --time_out_prep_mult                    0.1
% 35.85/4.99  --splitting_mode                        input
% 35.85/4.99  --splitting_grd                         true
% 35.85/4.99  --splitting_cvd                         false
% 35.85/4.99  --splitting_cvd_svl                     false
% 35.85/4.99  --splitting_nvd                         32
% 35.85/4.99  --sub_typing                            true
% 35.85/4.99  --prep_gs_sim                           true
% 35.85/4.99  --prep_unflatten                        true
% 35.85/4.99  --prep_res_sim                          true
% 35.85/4.99  --prep_upred                            true
% 35.85/4.99  --prep_sem_filter                       exhaustive
% 35.85/4.99  --prep_sem_filter_out                   false
% 35.85/4.99  --pred_elim                             true
% 35.85/4.99  --res_sim_input                         true
% 35.85/4.99  --eq_ax_congr_red                       true
% 35.85/4.99  --pure_diseq_elim                       true
% 35.85/4.99  --brand_transform                       false
% 35.85/4.99  --non_eq_to_eq                          false
% 35.85/4.99  --prep_def_merge                        true
% 35.85/4.99  --prep_def_merge_prop_impl              false
% 35.85/4.99  --prep_def_merge_mbd                    true
% 35.85/4.99  --prep_def_merge_tr_red                 false
% 35.85/4.99  --prep_def_merge_tr_cl                  false
% 35.85/4.99  --smt_preprocessing                     true
% 35.85/4.99  --smt_ac_axioms                         fast
% 35.85/4.99  --preprocessed_out                      false
% 35.85/4.99  --preprocessed_stats                    false
% 35.85/4.99  
% 35.85/4.99  ------ Abstraction refinement Options
% 35.85/4.99  
% 35.85/4.99  --abstr_ref                             []
% 35.85/4.99  --abstr_ref_prep                        false
% 35.85/4.99  --abstr_ref_until_sat                   false
% 35.85/4.99  --abstr_ref_sig_restrict                funpre
% 35.85/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.85/4.99  --abstr_ref_under                       []
% 35.85/4.99  
% 35.85/4.99  ------ SAT Options
% 35.85/4.99  
% 35.85/4.99  --sat_mode                              false
% 35.85/4.99  --sat_fm_restart_options                ""
% 35.85/4.99  --sat_gr_def                            false
% 35.85/4.99  --sat_epr_types                         true
% 35.85/4.99  --sat_non_cyclic_types                  false
% 35.85/4.99  --sat_finite_models                     false
% 35.85/4.99  --sat_fm_lemmas                         false
% 35.85/4.99  --sat_fm_prep                           false
% 35.85/4.99  --sat_fm_uc_incr                        true
% 35.85/4.99  --sat_out_model                         small
% 35.85/4.99  --sat_out_clauses                       false
% 35.85/4.99  
% 35.85/4.99  ------ QBF Options
% 35.85/4.99  
% 35.85/4.99  --qbf_mode                              false
% 35.85/4.99  --qbf_elim_univ                         false
% 35.85/4.99  --qbf_dom_inst                          none
% 35.85/4.99  --qbf_dom_pre_inst                      false
% 35.85/4.99  --qbf_sk_in                             false
% 35.85/4.99  --qbf_pred_elim                         true
% 35.85/4.99  --qbf_split                             512
% 35.85/4.99  
% 35.85/4.99  ------ BMC1 Options
% 35.85/4.99  
% 35.85/4.99  --bmc1_incremental                      false
% 35.85/4.99  --bmc1_axioms                           reachable_all
% 35.85/4.99  --bmc1_min_bound                        0
% 35.85/4.99  --bmc1_max_bound                        -1
% 35.85/4.99  --bmc1_max_bound_default                -1
% 35.85/4.99  --bmc1_symbol_reachability              true
% 35.85/4.99  --bmc1_property_lemmas                  false
% 35.85/4.99  --bmc1_k_induction                      false
% 35.85/4.99  --bmc1_non_equiv_states                 false
% 35.85/4.99  --bmc1_deadlock                         false
% 35.85/4.99  --bmc1_ucm                              false
% 35.85/4.99  --bmc1_add_unsat_core                   none
% 35.85/4.99  --bmc1_unsat_core_children              false
% 35.85/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.85/4.99  --bmc1_out_stat                         full
% 35.85/4.99  --bmc1_ground_init                      false
% 35.85/4.99  --bmc1_pre_inst_next_state              false
% 35.85/4.99  --bmc1_pre_inst_state                   false
% 35.85/4.99  --bmc1_pre_inst_reach_state             false
% 35.85/4.99  --bmc1_out_unsat_core                   false
% 35.85/4.99  --bmc1_aig_witness_out                  false
% 35.85/4.99  --bmc1_verbose                          false
% 35.85/4.99  --bmc1_dump_clauses_tptp                false
% 35.85/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.85/4.99  --bmc1_dump_file                        -
% 35.85/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.85/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.85/4.99  --bmc1_ucm_extend_mode                  1
% 35.85/4.99  --bmc1_ucm_init_mode                    2
% 35.85/4.99  --bmc1_ucm_cone_mode                    none
% 35.85/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.85/4.99  --bmc1_ucm_relax_model                  4
% 35.85/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.85/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.85/4.99  --bmc1_ucm_layered_model                none
% 35.85/4.99  --bmc1_ucm_max_lemma_size               10
% 35.85/4.99  
% 35.85/4.99  ------ AIG Options
% 35.85/4.99  
% 35.85/4.99  --aig_mode                              false
% 35.85/4.99  
% 35.85/4.99  ------ Instantiation Options
% 35.85/4.99  
% 35.85/4.99  --instantiation_flag                    true
% 35.85/4.99  --inst_sos_flag                         true
% 35.85/4.99  --inst_sos_phase                        true
% 35.85/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.85/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.85/4.99  --inst_lit_sel_side                     num_symb
% 35.85/4.99  --inst_solver_per_active                1400
% 35.85/4.99  --inst_solver_calls_frac                1.
% 35.85/4.99  --inst_passive_queue_type               priority_queues
% 35.85/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.85/4.99  --inst_passive_queues_freq              [25;2]
% 35.85/4.99  --inst_dismatching                      true
% 35.85/4.99  --inst_eager_unprocessed_to_passive     true
% 35.85/4.99  --inst_prop_sim_given                   true
% 35.85/4.99  --inst_prop_sim_new                     false
% 35.85/4.99  --inst_subs_new                         false
% 35.85/4.99  --inst_eq_res_simp                      false
% 35.85/4.99  --inst_subs_given                       false
% 35.85/4.99  --inst_orphan_elimination               true
% 35.85/4.99  --inst_learning_loop_flag               true
% 35.85/4.99  --inst_learning_start                   3000
% 35.85/4.99  --inst_learning_factor                  2
% 35.85/4.99  --inst_start_prop_sim_after_learn       3
% 35.85/4.99  --inst_sel_renew                        solver
% 35.85/4.99  --inst_lit_activity_flag                true
% 35.85/4.99  --inst_restr_to_given                   false
% 35.85/4.99  --inst_activity_threshold               500
% 35.85/4.99  --inst_out_proof                        true
% 35.85/4.99  
% 35.85/4.99  ------ Resolution Options
% 35.85/4.99  
% 35.85/4.99  --resolution_flag                       true
% 35.85/4.99  --res_lit_sel                           adaptive
% 35.85/4.99  --res_lit_sel_side                      none
% 35.85/4.99  --res_ordering                          kbo
% 35.85/4.99  --res_to_prop_solver                    active
% 35.85/4.99  --res_prop_simpl_new                    false
% 35.85/4.99  --res_prop_simpl_given                  true
% 35.85/4.99  --res_passive_queue_type                priority_queues
% 35.85/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.85/4.99  --res_passive_queues_freq               [15;5]
% 35.85/4.99  --res_forward_subs                      full
% 35.85/4.99  --res_backward_subs                     full
% 35.85/4.99  --res_forward_subs_resolution           true
% 35.85/4.99  --res_backward_subs_resolution          true
% 35.85/4.99  --res_orphan_elimination                true
% 35.85/4.99  --res_time_limit                        2.
% 35.85/4.99  --res_out_proof                         true
% 35.85/4.99  
% 35.85/4.99  ------ Superposition Options
% 35.85/4.99  
% 35.85/4.99  --superposition_flag                    true
% 35.85/4.99  --sup_passive_queue_type                priority_queues
% 35.85/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.85/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.85/4.99  --demod_completeness_check              fast
% 35.85/4.99  --demod_use_ground                      true
% 35.85/4.99  --sup_to_prop_solver                    passive
% 35.85/4.99  --sup_prop_simpl_new                    true
% 35.85/4.99  --sup_prop_simpl_given                  true
% 35.85/4.99  --sup_fun_splitting                     true
% 35.85/4.99  --sup_smt_interval                      50000
% 35.85/4.99  
% 35.85/4.99  ------ Superposition Simplification Setup
% 35.85/4.99  
% 35.85/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.85/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.85/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.85/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.85/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.85/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.85/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.85/4.99  --sup_immed_triv                        [TrivRules]
% 35.85/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_immed_bw_main                     []
% 35.85/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.85/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.85/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_input_bw                          []
% 35.85/4.99  
% 35.85/4.99  ------ Combination Options
% 35.85/4.99  
% 35.85/4.99  --comb_res_mult                         3
% 35.85/4.99  --comb_sup_mult                         2
% 35.85/4.99  --comb_inst_mult                        10
% 35.85/4.99  
% 35.85/4.99  ------ Debug Options
% 35.85/4.99  
% 35.85/4.99  --dbg_backtrace                         false
% 35.85/4.99  --dbg_dump_prop_clauses                 false
% 35.85/4.99  --dbg_dump_prop_clauses_file            -
% 35.85/4.99  --dbg_out_stat                          false
% 35.85/4.99  ------ Parsing...
% 35.85/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.85/4.99  ------ Proving...
% 35.85/4.99  ------ Problem Properties 
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  clauses                                 33
% 35.85/4.99  conjectures                             8
% 35.85/4.99  EPR                                     3
% 35.85/4.99  Horn                                    24
% 35.85/4.99  unary                                   4
% 35.85/4.99  binary                                  5
% 35.85/4.99  lits                                    105
% 35.85/4.99  lits eq                                 8
% 35.85/4.99  fd_pure                                 0
% 35.85/4.99  fd_pseudo                               0
% 35.85/4.99  fd_cond                                 0
% 35.85/4.99  fd_pseudo_cond                          3
% 35.85/4.99  AC symbols                              0
% 35.85/4.99  
% 35.85/4.99  ------ Schedule dynamic 5 is on 
% 35.85/4.99  
% 35.85/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  ------ 
% 35.85/4.99  Current options:
% 35.85/4.99  ------ 
% 35.85/4.99  
% 35.85/4.99  ------ Input Options
% 35.85/4.99  
% 35.85/4.99  --out_options                           all
% 35.85/4.99  --tptp_safe_out                         true
% 35.85/4.99  --problem_path                          ""
% 35.85/4.99  --include_path                          ""
% 35.85/4.99  --clausifier                            res/vclausify_rel
% 35.85/4.99  --clausifier_options                    ""
% 35.85/4.99  --stdin                                 false
% 35.85/4.99  --stats_out                             all
% 35.85/4.99  
% 35.85/4.99  ------ General Options
% 35.85/4.99  
% 35.85/4.99  --fof                                   false
% 35.85/4.99  --time_out_real                         305.
% 35.85/4.99  --time_out_virtual                      -1.
% 35.85/4.99  --symbol_type_check                     false
% 35.85/4.99  --clausify_out                          false
% 35.85/4.99  --sig_cnt_out                           false
% 35.85/4.99  --trig_cnt_out                          false
% 35.85/4.99  --trig_cnt_out_tolerance                1.
% 35.85/4.99  --trig_cnt_out_sk_spl                   false
% 35.85/4.99  --abstr_cl_out                          false
% 35.85/4.99  
% 35.85/4.99  ------ Global Options
% 35.85/4.99  
% 35.85/4.99  --schedule                              default
% 35.85/4.99  --add_important_lit                     false
% 35.85/4.99  --prop_solver_per_cl                    1000
% 35.85/4.99  --min_unsat_core                        false
% 35.85/4.99  --soft_assumptions                      false
% 35.85/4.99  --soft_lemma_size                       3
% 35.85/4.99  --prop_impl_unit_size                   0
% 35.85/4.99  --prop_impl_unit                        []
% 35.85/4.99  --share_sel_clauses                     true
% 35.85/4.99  --reset_solvers                         false
% 35.85/4.99  --bc_imp_inh                            [conj_cone]
% 35.85/4.99  --conj_cone_tolerance                   3.
% 35.85/4.99  --extra_neg_conj                        none
% 35.85/4.99  --large_theory_mode                     true
% 35.85/4.99  --prolific_symb_bound                   200
% 35.85/4.99  --lt_threshold                          2000
% 35.85/4.99  --clause_weak_htbl                      true
% 35.85/4.99  --gc_record_bc_elim                     false
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing Options
% 35.85/4.99  
% 35.85/4.99  --preprocessing_flag                    true
% 35.85/4.99  --time_out_prep_mult                    0.1
% 35.85/4.99  --splitting_mode                        input
% 35.85/4.99  --splitting_grd                         true
% 35.85/4.99  --splitting_cvd                         false
% 35.85/4.99  --splitting_cvd_svl                     false
% 35.85/4.99  --splitting_nvd                         32
% 35.85/4.99  --sub_typing                            true
% 35.85/4.99  --prep_gs_sim                           true
% 35.85/4.99  --prep_unflatten                        true
% 35.85/4.99  --prep_res_sim                          true
% 35.85/4.99  --prep_upred                            true
% 35.85/4.99  --prep_sem_filter                       exhaustive
% 35.85/4.99  --prep_sem_filter_out                   false
% 35.85/4.99  --pred_elim                             true
% 35.85/4.99  --res_sim_input                         true
% 35.85/4.99  --eq_ax_congr_red                       true
% 35.85/4.99  --pure_diseq_elim                       true
% 35.85/4.99  --brand_transform                       false
% 35.85/4.99  --non_eq_to_eq                          false
% 35.85/4.99  --prep_def_merge                        true
% 35.85/4.99  --prep_def_merge_prop_impl              false
% 35.85/4.99  --prep_def_merge_mbd                    true
% 35.85/4.99  --prep_def_merge_tr_red                 false
% 35.85/4.99  --prep_def_merge_tr_cl                  false
% 35.85/4.99  --smt_preprocessing                     true
% 35.85/4.99  --smt_ac_axioms                         fast
% 35.85/4.99  --preprocessed_out                      false
% 35.85/4.99  --preprocessed_stats                    false
% 35.85/4.99  
% 35.85/4.99  ------ Abstraction refinement Options
% 35.85/4.99  
% 35.85/4.99  --abstr_ref                             []
% 35.85/4.99  --abstr_ref_prep                        false
% 35.85/4.99  --abstr_ref_until_sat                   false
% 35.85/4.99  --abstr_ref_sig_restrict                funpre
% 35.85/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.85/4.99  --abstr_ref_under                       []
% 35.85/4.99  
% 35.85/4.99  ------ SAT Options
% 35.85/4.99  
% 35.85/4.99  --sat_mode                              false
% 35.85/4.99  --sat_fm_restart_options                ""
% 35.85/4.99  --sat_gr_def                            false
% 35.85/4.99  --sat_epr_types                         true
% 35.85/4.99  --sat_non_cyclic_types                  false
% 35.85/4.99  --sat_finite_models                     false
% 35.85/4.99  --sat_fm_lemmas                         false
% 35.85/4.99  --sat_fm_prep                           false
% 35.85/4.99  --sat_fm_uc_incr                        true
% 35.85/4.99  --sat_out_model                         small
% 35.85/4.99  --sat_out_clauses                       false
% 35.85/4.99  
% 35.85/4.99  ------ QBF Options
% 35.85/4.99  
% 35.85/4.99  --qbf_mode                              false
% 35.85/4.99  --qbf_elim_univ                         false
% 35.85/4.99  --qbf_dom_inst                          none
% 35.85/4.99  --qbf_dom_pre_inst                      false
% 35.85/4.99  --qbf_sk_in                             false
% 35.85/4.99  --qbf_pred_elim                         true
% 35.85/4.99  --qbf_split                             512
% 35.85/4.99  
% 35.85/4.99  ------ BMC1 Options
% 35.85/4.99  
% 35.85/4.99  --bmc1_incremental                      false
% 35.85/4.99  --bmc1_axioms                           reachable_all
% 35.85/4.99  --bmc1_min_bound                        0
% 35.85/4.99  --bmc1_max_bound                        -1
% 35.85/4.99  --bmc1_max_bound_default                -1
% 35.85/4.99  --bmc1_symbol_reachability              true
% 35.85/4.99  --bmc1_property_lemmas                  false
% 35.85/4.99  --bmc1_k_induction                      false
% 35.85/4.99  --bmc1_non_equiv_states                 false
% 35.85/4.99  --bmc1_deadlock                         false
% 35.85/4.99  --bmc1_ucm                              false
% 35.85/4.99  --bmc1_add_unsat_core                   none
% 35.85/4.99  --bmc1_unsat_core_children              false
% 35.85/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.85/4.99  --bmc1_out_stat                         full
% 35.85/4.99  --bmc1_ground_init                      false
% 35.85/4.99  --bmc1_pre_inst_next_state              false
% 35.85/4.99  --bmc1_pre_inst_state                   false
% 35.85/4.99  --bmc1_pre_inst_reach_state             false
% 35.85/4.99  --bmc1_out_unsat_core                   false
% 35.85/4.99  --bmc1_aig_witness_out                  false
% 35.85/4.99  --bmc1_verbose                          false
% 35.85/4.99  --bmc1_dump_clauses_tptp                false
% 35.85/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.85/4.99  --bmc1_dump_file                        -
% 35.85/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.85/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.85/4.99  --bmc1_ucm_extend_mode                  1
% 35.85/4.99  --bmc1_ucm_init_mode                    2
% 35.85/4.99  --bmc1_ucm_cone_mode                    none
% 35.85/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.85/4.99  --bmc1_ucm_relax_model                  4
% 35.85/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.85/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.85/4.99  --bmc1_ucm_layered_model                none
% 35.85/4.99  --bmc1_ucm_max_lemma_size               10
% 35.85/4.99  
% 35.85/4.99  ------ AIG Options
% 35.85/4.99  
% 35.85/4.99  --aig_mode                              false
% 35.85/4.99  
% 35.85/4.99  ------ Instantiation Options
% 35.85/4.99  
% 35.85/4.99  --instantiation_flag                    true
% 35.85/4.99  --inst_sos_flag                         true
% 35.85/4.99  --inst_sos_phase                        true
% 35.85/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.85/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.85/4.99  --inst_lit_sel_side                     none
% 35.85/4.99  --inst_solver_per_active                1400
% 35.85/4.99  --inst_solver_calls_frac                1.
% 35.85/4.99  --inst_passive_queue_type               priority_queues
% 35.85/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.85/4.99  --inst_passive_queues_freq              [25;2]
% 35.85/4.99  --inst_dismatching                      true
% 35.85/4.99  --inst_eager_unprocessed_to_passive     true
% 35.85/4.99  --inst_prop_sim_given                   true
% 35.85/4.99  --inst_prop_sim_new                     false
% 35.85/4.99  --inst_subs_new                         false
% 35.85/4.99  --inst_eq_res_simp                      false
% 35.85/4.99  --inst_subs_given                       false
% 35.85/4.99  --inst_orphan_elimination               true
% 35.85/4.99  --inst_learning_loop_flag               true
% 35.85/4.99  --inst_learning_start                   3000
% 35.85/4.99  --inst_learning_factor                  2
% 35.85/4.99  --inst_start_prop_sim_after_learn       3
% 35.85/4.99  --inst_sel_renew                        solver
% 35.85/4.99  --inst_lit_activity_flag                true
% 35.85/4.99  --inst_restr_to_given                   false
% 35.85/4.99  --inst_activity_threshold               500
% 35.85/4.99  --inst_out_proof                        true
% 35.85/4.99  
% 35.85/4.99  ------ Resolution Options
% 35.85/4.99  
% 35.85/4.99  --resolution_flag                       false
% 35.85/4.99  --res_lit_sel                           adaptive
% 35.85/4.99  --res_lit_sel_side                      none
% 35.85/4.99  --res_ordering                          kbo
% 35.85/4.99  --res_to_prop_solver                    active
% 35.85/4.99  --res_prop_simpl_new                    false
% 35.85/4.99  --res_prop_simpl_given                  true
% 35.85/4.99  --res_passive_queue_type                priority_queues
% 35.85/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.85/4.99  --res_passive_queues_freq               [15;5]
% 35.85/4.99  --res_forward_subs                      full
% 35.85/4.99  --res_backward_subs                     full
% 35.85/4.99  --res_forward_subs_resolution           true
% 35.85/4.99  --res_backward_subs_resolution          true
% 35.85/4.99  --res_orphan_elimination                true
% 35.85/4.99  --res_time_limit                        2.
% 35.85/4.99  --res_out_proof                         true
% 35.85/4.99  
% 35.85/4.99  ------ Superposition Options
% 35.85/4.99  
% 35.85/4.99  --superposition_flag                    true
% 35.85/4.99  --sup_passive_queue_type                priority_queues
% 35.85/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.85/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.85/4.99  --demod_completeness_check              fast
% 35.85/4.99  --demod_use_ground                      true
% 35.85/4.99  --sup_to_prop_solver                    passive
% 35.85/4.99  --sup_prop_simpl_new                    true
% 35.85/4.99  --sup_prop_simpl_given                  true
% 35.85/4.99  --sup_fun_splitting                     true
% 35.85/4.99  --sup_smt_interval                      50000
% 35.85/4.99  
% 35.85/4.99  ------ Superposition Simplification Setup
% 35.85/4.99  
% 35.85/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.85/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.85/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.85/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.85/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.85/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.85/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.85/4.99  --sup_immed_triv                        [TrivRules]
% 35.85/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_immed_bw_main                     []
% 35.85/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.85/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.85/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.85/4.99  --sup_input_bw                          []
% 35.85/4.99  
% 35.85/4.99  ------ Combination Options
% 35.85/4.99  
% 35.85/4.99  --comb_res_mult                         3
% 35.85/4.99  --comb_sup_mult                         2
% 35.85/4.99  --comb_inst_mult                        10
% 35.85/4.99  
% 35.85/4.99  ------ Debug Options
% 35.85/4.99  
% 35.85/4.99  --dbg_backtrace                         false
% 35.85/4.99  --dbg_dump_prop_clauses                 false
% 35.85/4.99  --dbg_dump_prop_clauses_file            -
% 35.85/4.99  --dbg_out_stat                          false
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  ------ Proving...
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  % SZS status Theorem for theBenchmark.p
% 35.85/4.99  
% 35.85/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.85/4.99  
% 35.85/4.99  fof(f9,axiom,(
% 35.85/4.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f24,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(ennf_transformation,[],[f9])).
% 35.85/4.99  
% 35.85/4.99  fof(f25,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(flattening,[],[f24])).
% 35.85/4.99  
% 35.85/4.99  fof(f34,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(nnf_transformation,[],[f25])).
% 35.85/4.99  
% 35.85/4.99  fof(f35,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(rectify,[],[f34])).
% 35.85/4.99  
% 35.85/4.99  fof(f36,plain,(
% 35.85/4.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f37,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 35.85/4.99  
% 35.85/4.99  fof(f61,plain,(
% 35.85/4.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f37])).
% 35.85/4.99  
% 35.85/4.99  fof(f13,conjecture,(
% 35.85/4.99    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f14,negated_conjecture,(
% 35.85/4.99    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 35.85/4.99    inference(negated_conjecture,[],[f13])).
% 35.85/4.99  
% 35.85/4.99  fof(f15,plain,(
% 35.85/4.99    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 35.85/4.99    inference(rectify,[],[f14])).
% 35.85/4.99  
% 35.85/4.99  fof(f31,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 35.85/4.99    inference(ennf_transformation,[],[f15])).
% 35.85/4.99  
% 35.85/4.99  fof(f32,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 35.85/4.99    inference(flattening,[],[f31])).
% 35.85/4.99  
% 35.85/4.99  fof(f43,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 35.85/4.99    inference(nnf_transformation,[],[f32])).
% 35.85/4.99  
% 35.85/4.99  fof(f44,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 35.85/4.99    inference(flattening,[],[f43])).
% 35.85/4.99  
% 35.85/4.99  fof(f45,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 35.85/4.99    inference(rectify,[],[f44])).
% 35.85/4.99  
% 35.85/4.99  fof(f50,plain,(
% 35.85/4.99    ( ! [X0,X1] : (! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k2_yellow_0(X0,sK6(X5)) = X5 & r2_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f49,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r1_lattice3(X0,X2,sK5) | ~r1_lattice3(X0,X1,sK5)) & (r1_lattice3(X0,X2,sK5) | r1_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f48,plain,(
% 35.85/4.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r1_lattice3(X0,sK4,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,sK4,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f47,plain,(
% 35.85/4.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,sK3,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f46,plain,(
% 35.85/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK2,X2,X3) | ~r1_lattice3(sK2,X1,X3)) & (r1_lattice3(sK2,X2,X3) | r1_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK2,X6) = X5 & r2_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f51,plain,(
% 35.85/4.99    ((((~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)) & (r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK2,sK6(X5)) = X5 & r2_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 35.85/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f45,f50,f49,f48,f47,f46])).
% 35.85/4.99  
% 35.85/4.99  fof(f79,plain,(
% 35.85/4.99    l1_orders_2(sK2)),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f3,axiom,(
% 35.85/4.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f16,plain,(
% 35.85/4.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.85/4.99    inference(ennf_transformation,[],[f3])).
% 35.85/4.99  
% 35.85/4.99  fof(f54,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f16])).
% 35.85/4.99  
% 35.85/4.99  fof(f62,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f37])).
% 35.85/4.99  
% 35.85/4.99  fof(f63,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f37])).
% 35.85/4.99  
% 35.85/4.99  fof(f64,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f37])).
% 35.85/4.99  
% 35.85/4.99  fof(f10,axiom,(
% 35.85/4.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f26,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(ennf_transformation,[],[f10])).
% 35.85/4.99  
% 35.85/4.99  fof(f27,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(flattening,[],[f26])).
% 35.85/4.99  
% 35.85/4.99  fof(f38,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(nnf_transformation,[],[f27])).
% 35.85/4.99  
% 35.85/4.99  fof(f39,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(flattening,[],[f38])).
% 35.85/4.99  
% 35.85/4.99  fof(f40,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(rectify,[],[f39])).
% 35.85/4.99  
% 35.85/4.99  fof(f41,plain,(
% 35.85/4.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 35.85/4.99    introduced(choice_axiom,[])).
% 35.85/4.99  
% 35.85/4.99  fof(f42,plain,(
% 35.85/4.99    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 35.85/4.99  
% 35.85/4.99  fof(f66,plain,(
% 35.85/4.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f42])).
% 35.85/4.99  
% 35.85/4.99  fof(f91,plain,(
% 35.85/4.99    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(equality_resolution,[],[f66])).
% 35.85/4.99  
% 35.85/4.99  fof(f81,plain,(
% 35.85/4.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f5,axiom,(
% 35.85/4.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f18,plain,(
% 35.85/4.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 35.85/4.99    inference(ennf_transformation,[],[f5])).
% 35.85/4.99  
% 35.85/4.99  fof(f19,plain,(
% 35.85/4.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 35.85/4.99    inference(flattening,[],[f18])).
% 35.85/4.99  
% 35.85/4.99  fof(f56,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f19])).
% 35.85/4.99  
% 35.85/4.99  fof(f80,plain,(
% 35.85/4.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f88,plain,(
% 35.85/4.99    m1_subset_1(sK5,u1_struct_0(sK2))),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f12,axiom,(
% 35.85/4.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f30,plain,(
% 35.85/4.99    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.85/4.99    inference(ennf_transformation,[],[f12])).
% 35.85/4.99  
% 35.85/4.99  fof(f73,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f30])).
% 35.85/4.99  
% 35.85/4.99  fof(f89,plain,(
% 35.85/4.99    r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f65,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f42])).
% 35.85/4.99  
% 35.85/4.99  fof(f92,plain,(
% 35.85/4.99    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(equality_resolution,[],[f65])).
% 35.85/4.99  
% 35.85/4.99  fof(f11,axiom,(
% 35.85/4.99    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f28,plain,(
% 35.85/4.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 35.85/4.99    inference(ennf_transformation,[],[f11])).
% 35.85/4.99  
% 35.85/4.99  fof(f29,plain,(
% 35.85/4.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 35.85/4.99    inference(flattening,[],[f28])).
% 35.85/4.99  
% 35.85/4.99  fof(f70,plain,(
% 35.85/4.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f29])).
% 35.85/4.99  
% 35.85/4.99  fof(f78,plain,(
% 35.85/4.99    v4_orders_2(sK2)),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f90,plain,(
% 35.85/4.99    ~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f4,axiom,(
% 35.85/4.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f17,plain,(
% 35.85/4.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 35.85/4.99    inference(ennf_transformation,[],[f4])).
% 35.85/4.99  
% 35.85/4.99  fof(f55,plain,(
% 35.85/4.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f17])).
% 35.85/4.99  
% 35.85/4.99  fof(f72,plain,(
% 35.85/4.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f30])).
% 35.85/4.99  
% 35.85/4.99  fof(f6,axiom,(
% 35.85/4.99    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f57,plain,(
% 35.85/4.99    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f6])).
% 35.85/4.99  
% 35.85/4.99  fof(f82,plain,(
% 35.85/4.99    ( ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f87,plain,(
% 35.85/4.99    ( ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f1,axiom,(
% 35.85/4.99    v1_xboole_0(k1_xboole_0)),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f52,plain,(
% 35.85/4.99    v1_xboole_0(k1_xboole_0)),
% 35.85/4.99    inference(cnf_transformation,[],[f1])).
% 35.85/4.99  
% 35.85/4.99  fof(f2,axiom,(
% 35.85/4.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 35.85/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.85/4.99  
% 35.85/4.99  fof(f53,plain,(
% 35.85/4.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f2])).
% 35.85/4.99  
% 35.85/4.99  fof(f86,plain,(
% 35.85/4.99    ( ! [X5] : (k2_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f84,plain,(
% 35.85/4.99    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  fof(f85,plain,(
% 35.85/4.99    ( ! [X5] : (r2_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 35.85/4.99    inference(cnf_transformation,[],[f51])).
% 35.85/4.99  
% 35.85/4.99  cnf(c_12,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(X0,X2,X3)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/4.99      | ~ r2_hidden(X3,X1)
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f61]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_35,negated_conjecture,
% 35.85/4.99      ( l1_orders_2(sK2) ),
% 35.85/4.99      inference(cnf_transformation,[],[f79]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_913,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(X0,X2,X3)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/4.99      | ~ r2_hidden(X3,X1)
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_914,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_orders_2(sK2,X1,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(X2,X0) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_913]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_68278,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_orders_2(sK2,X1,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1))
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1),u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X1),X0) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_914]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_83834,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,sK3,sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5))
% 35.85/4.99      | ~ m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_68278]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3189,plain,
% 35.85/4.99      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(X3,X4,X5)
% 35.85/4.99      | X3 != X0
% 35.85/4.99      | X4 != X1
% 35.85/4.99      | X5 != X2 ),
% 35.85/4.99      theory(equality) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58232,plain,
% 35.85/4.99      ( ~ r1_orders_2(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 35.85/4.99      | sK0(sK2,sK4,sK5) != X2
% 35.85/4.99      | sK5 != X1
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3189]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58572,plain,
% 35.85/4.99      ( ~ r1_orders_2(X0,sK5,X1)
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 35.85/4.99      | sK0(sK2,sK4,sK5) != X1
% 35.85/4.99      | sK5 != sK5
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58232]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_67049,plain,
% 35.85/4.99      ( ~ r1_orders_2(X0,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 35.85/4.99      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | sK5 != sK5
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58572]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_67051,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 35.85/4.99      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | sK5 != sK5
% 35.85/4.99      | sK2 != sK2 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_67049]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_2,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.85/4.99      | ~ r2_hidden(X2,X0)
% 35.85/4.99      | r2_hidden(X2,X1) ),
% 35.85/4.99      inference(cnf_transformation,[],[f54]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58370,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(X1,X0)
% 35.85/4.99      | r2_hidden(X1,sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_59224,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(X0,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | r2_hidden(X0,sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58370]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_59645,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_59224]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_64542,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_59645]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f62]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_932,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_933,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_932]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58781,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_933]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_61588,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58781]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_10,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f63]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_947,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_948,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_947]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58780,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0),sK6(sK0(sK2,sK4,sK5))) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_948]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_60438,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5),sK6(sK0(sK2,sK4,sK5))) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58780]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_9,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f64]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_962,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,X2)
% 35.85/4.99      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_963,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_962]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58779,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 35.85/4.99      | ~ r1_orders_2(sK2,X0,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),X0))
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_963]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_60408,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK6(sK0(sK2,sK4,sK5)),sK5))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58779]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_16,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 35.85/4.99      | ~ r2_yellow_0(X0,X1)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f91]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_829,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 35.85/4.99      | ~ r2_yellow_0(X0,X1)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_830,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 35.85/4.99      | ~ r2_yellow_0(sK2,X0)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_829]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_58293,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 35.85/4.99      | r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 35.85/4.99      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_830]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_59818,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 35.85/4.99      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_58293]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3910,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_33,negated_conjecture,
% 35.85/4.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 35.85/4.99      inference(cnf_transformation,[],[f81]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3931,plain,
% 35.85/4.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4,plain,
% 35.85/4.99      ( m1_subset_1(X0,X1)
% 35.85/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.85/4.99      | ~ r2_hidden(X0,X2) ),
% 35.85/4.99      inference(cnf_transformation,[],[f56]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3938,plain,
% 35.85/4.99      ( m1_subset_1(X0,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,X2) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4288,plain,
% 35.85/4.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3931,c_3938]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3916,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5283,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_3916]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_34,negated_conjecture,
% 35.85/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 35.85/4.99      inference(cnf_transformation,[],[f80]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3930,plain,
% 35.85/4.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4289,plain,
% 35.85/4.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3930,c_3938]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_26,negated_conjecture,
% 35.85/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(cnf_transformation,[],[f88]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3935,plain,
% 35.85/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_22,plain,
% 35.85/4.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 35.85/4.99      | ~ r1_orders_2(X0,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f73]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_762,plain,
% 35.85/4.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 35.85/4.99      | ~ r1_orders_2(X0,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_763,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(X0),X1)
% 35.85/4.99      | ~ r1_orders_2(sK2,X1,X0)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_762]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3920,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3912,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,X2) = iProver_top
% 35.85/4.99      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X2,X0) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4975,plain,
% 35.85/4.99      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X0,X2) = iProver_top
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X2,k1_tarski(X1)) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3920,c_3912]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_6540,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3935,c_4975]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_6563,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X1,k1_tarski(X0)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_6540]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_7009,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r2_hidden(X1,k1_tarski(X0)) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4289,c_6563]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_7421,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X1,k1_tarski(k2_yellow_0(sK2,X0))) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_5283,c_7009]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_63,plain,
% 35.85/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_25,negated_conjecture,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 35.85/4.99      inference(cnf_transformation,[],[f89]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3936,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 35.85/4.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4974,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3936,c_3912]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5039,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_4974,c_63,c_4289]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5046,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_5039,c_3912]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11110,plain,
% 35.85/4.99      ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK4) != iProver_top ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_5046,c_63]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11111,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK4) != iProver_top ),
% 35.85/4.99      inference(renaming,[status(thm)],[c_11110]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11118,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r2_hidden(X1,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_11111]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_17,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 35.85/4.99      | ~ r2_yellow_0(X0,X1)
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f92]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_814,plain,
% 35.85/4.99      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 35.85/4.99      | ~ r2_yellow_0(X0,X1)
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_815,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 35.85/4.99      | ~ r2_yellow_0(sK2,X0)
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_814]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3917,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4699,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_3917]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_19,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_lattice3(X0,X1,X3)
% 35.85/4.99      | ~ r1_orders_2(X0,X3,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/4.99      | ~ v4_orders_2(X0)
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f70]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_36,negated_conjecture,
% 35.85/4.99      ( v4_orders_2(sK2) ),
% 35.85/4.99      inference(cnf_transformation,[],[f78]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_507,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,X1,X2)
% 35.85/4.99      | r1_lattice3(X0,X1,X3)
% 35.85/4.99      | ~ r1_orders_2(X0,X3,X2)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0)
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_508,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_lattice3(sK2,X0,X2)
% 35.85/4.99      | ~ r1_orders_2(sK2,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ l1_orders_2(sK2) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_507]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_510,plain,
% 35.85/4.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | ~ r1_orders_2(sK2,X2,X1)
% 35.85/4.99      | r1_lattice3(sK2,X0,X2)
% 35.85/4.99      | ~ r1_lattice3(sK2,X0,X1) ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_508,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_511,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_lattice3(sK2,X0,X2)
% 35.85/4.99      | ~ r1_orders_2(sK2,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(renaming,[status(thm)],[c_510]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3929,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 35.85/4.99      | r1_lattice3(sK2,X0,X2) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X2,X1) != iProver_top
% 35.85/4.99      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5607,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4699,c_3929]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11682,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) != iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_5607]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_11737,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_11118,c_11682]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_47921,plain,
% 35.85/4.99      ( r2_yellow_0(sK2,X0) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1) = iProver_top
% 35.85/4.99      | r2_hidden(X1,k1_tarski(k2_yellow_0(sK2,X0))) != iProver_top
% 35.85/4.99      | r2_hidden(X1,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4) != iProver_top ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_7421,c_63,c_11737]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_47922,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,X1) != iProver_top
% 35.85/4.99      | r2_hidden(X0,k1_tarski(k2_yellow_0(sK2,X1))) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X1),sK4) != iProver_top ),
% 35.85/4.99      inference(renaming,[status(thm)],[c_47921]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_44,plain,
% 35.85/4.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_24,negated_conjecture,
% 35.85/4.99      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 35.85/4.99      inference(cnf_transformation,[],[f90]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_65,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 35.85/4.99      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4044,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5)
% 35.85/4.99      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_933]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4185,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5)
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4044]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4186,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4185]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4094,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,sK0(sK2,X0,sK5))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_963]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4184,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4094]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4188,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4184]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4087,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5)
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,X0,sK5),X0) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_948]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4183,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5)
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4087]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4190,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4183]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3,plain,
% 35.85/4.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 35.85/4.99      inference(cnf_transformation,[],[f55]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4019,plain,
% 35.85/4.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(X0,sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4336,plain,
% 35.85/4.99      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4019]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4337,plain,
% 35.85/4.99      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 35.85/4.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4336]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_23,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 35.85/4.99      | r1_orders_2(X0,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | ~ l1_orders_2(X0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f72]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_744,plain,
% 35.85/4.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 35.85/4.99      | r1_orders_2(X0,X2,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.85/4.99      | sK2 != X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_745,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
% 35.85/4.99      | r1_orders_2(sK2,X1,X0)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_744]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4059,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,k1_tarski(X0),sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,X0)
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_745]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4543,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
% 35.85/4.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4059]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4547,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4543]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5,plain,
% 35.85/4.99      ( v1_finset_1(k1_tarski(X0)) ),
% 35.85/4.99      inference(cnf_transformation,[],[f57]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_32,negated_conjecture,
% 35.85/4.99      ( r2_yellow_0(sK2,X0)
% 35.85/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ v1_finset_1(X0)
% 35.85/4.99      | k1_xboole_0 = X0 ),
% 35.85/4.99      inference(cnf_transformation,[],[f82]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_565,plain,
% 35.85/4.99      ( r2_yellow_0(sK2,X0)
% 35.85/4.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 35.85/4.99      | k1_tarski(X1) != X0
% 35.85/4.99      | k1_xboole_0 = X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_5,c_32]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_566,plain,
% 35.85/4.99      ( r2_yellow_0(sK2,k1_tarski(X0))
% 35.85/4.99      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 35.85/4.99      | k1_xboole_0 = k1_tarski(X0) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_565]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4621,plain,
% 35.85/4.99      ( r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 35.85/4.99      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_566]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4622,plain,
% 35.85/4.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 35.85/4.99      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 35.85/4.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4621]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_27,negated_conjecture,
% 35.85/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 35.85/4.99      | ~ v1_finset_1(X0)
% 35.85/4.99      | k1_xboole_0 = X0 ),
% 35.85/4.99      inference(cnf_transformation,[],[f87]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_580,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 35.85/4.99      | k1_tarski(X1) != X0
% 35.85/4.99      | k1_xboole_0 = X0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_581,plain,
% 35.85/4.99      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
% 35.85/4.99      | k1_xboole_0 = k1_tarski(X0) ),
% 35.85/4.99      inference(unflattening,[status(thm)],[c_580]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4620,plain,
% 35.85/4.99      ( ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 35.85/4.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_581]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4624,plain,
% 35.85/4.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 35.85/4.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3184,plain,( X0 = X0 ),theory(equality) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_8049,plain,
% 35.85/4.99      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3184]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3185,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_6670,plain,
% 35.85/4.99      ( X0 != X1
% 35.85/4.99      | k1_tarski(sK0(sK2,sK3,sK5)) != X1
% 35.85/4.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3185]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_8101,plain,
% 35.85/4.99      ( X0 != k1_tarski(sK0(sK2,sK3,sK5))
% 35.85/4.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0
% 35.85/4.99      | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_6670]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_12954,plain,
% 35.85/4.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 35.85/4.99      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 35.85/4.99      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_8101]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4789,plain,
% 35.85/4.99      ( m1_subset_1(X0,u1_struct_0(X1))
% 35.85/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.85/4.99      | ~ r2_hidden(X0,X2) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_15106,plain,
% 35.85/4.99      ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(X0))
% 35.85/4.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 35.85/4.99      | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4789]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_15107,plain,
% 35.85/4.99      ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(X0)) = iProver_top
% 35.85/4.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_15106]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_15109,plain,
% 35.85/4.99      ( m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top
% 35.85/4.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_15107]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_15156,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 35.85/4.99      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_815]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_15157,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
% 35.85/4.99      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_15156]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4104,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,X1)
% 35.85/4.99      | r1_lattice3(sK2,X0,sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_511]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_5584,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0)
% 35.85/4.99      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,X0)
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4104]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_18734,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 35.85/4.99      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_5584]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_18741,plain,
% 35.85/4.99      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
% 35.85/4.99      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_18734]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_0,plain,
% 35.85/4.99      ( v1_xboole_0(k1_xboole_0) ),
% 35.85/4.99      inference(cnf_transformation,[],[f52]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_1,plain,
% 35.85/4.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 35.85/4.99      inference(cnf_transformation,[],[f53]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_501,plain,
% 35.85/4.99      ( k1_tarski(X0) != k1_xboole_0 ),
% 35.85/4.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_23663,plain,
% 35.85/4.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_501]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_14260,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,X0,sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,X1)
% 35.85/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(X1,X0) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_914]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_46021,plain,
% 35.85/4.99      ( ~ r1_lattice3(sK2,sK4,sK5)
% 35.85/4.99      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))))
% 35.85/4.99      | ~ m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),sK4) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_14260]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_46022,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5)))) = iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(X0,sK3,sK5))),sK4) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_46021]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_46024,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_46022]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_47927,plain,
% 35.85/4.99      ( r2_hidden(X0,sK3) != iProver_top
% 35.85/4.99      | r1_orders_2(sK2,sK5,X0) = iProver_top ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_47922,c_44,c_63,c_65,c_4186,c_4188,c_4190,c_4337,
% 35.85/4.99                 c_4547,c_4622,c_4624,c_5039,c_8049,c_12954,c_15109,
% 35.85/4.99                 c_15157,c_18741,c_23663,c_46024]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_47928,plain,
% 35.85/4.99      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 35.85/4.99      | r2_hidden(X0,sK3) != iProver_top ),
% 35.85/4.99      inference(renaming,[status(thm)],[c_47927]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3909,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 35.85/4.99      | r1_orders_2(sK2,X1,sK0(sK2,X0,X1)) != iProver_top
% 35.85/4.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_47961,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_47928,c_3909]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_48834,plain,
% 35.85/4.99      ( r1_lattice3(sK2,X0,sK5) = iProver_top
% 35.85/4.99      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top ),
% 35.85/4.99      inference(global_propositional_subsumption,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_47961,c_63]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_48840,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 35.85/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3910,c_48834]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_48844,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK3,sK5) | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(predicate_to_equality_rev,[status(thm)],[c_48840]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3188,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.85/4.99      theory(equality) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4054,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,X1)
% 35.85/4.99      | m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | X2 != X0
% 35.85/4.99      | u1_struct_0(sK2) != X1 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3188]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4264,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/4.99      | m1_subset_1(X2,u1_struct_0(sK2))
% 35.85/4.99      | X2 != X0
% 35.85/4.99      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4054]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_13917,plain,
% 35.85/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != X0
% 35.85/4.99      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4264]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_27474,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(X0))
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 35.85/4.99      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_13917]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_27476,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 35.85/4.99      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 35.85/4.99      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 35.85/4.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_27474]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_8082,plain,
% 35.85/4.99      ( X0 != X1 | sK0(sK2,sK4,sK5) != X1 | sK0(sK2,sK4,sK5) = X0 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3185]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_16594,plain,
% 35.85/4.99      ( X0 != sK0(X1,sK4,sK5)
% 35.85/4.99      | sK0(sK2,sK4,sK5) = X0
% 35.85/4.99      | sK0(sK2,sK4,sK5) != sK0(X1,sK4,sK5) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_8082]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_20571,plain,
% 35.85/4.99      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 35.85/4.99      | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_16594]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_8148,plain,
% 35.85/4.99      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3184]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_28,negated_conjecture,
% 35.85/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(X0,sK4)
% 35.85/4.99      | k2_yellow_0(sK2,sK6(X0)) = X0 ),
% 35.85/4.99      inference(cnf_transformation,[],[f86]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3934,plain,
% 35.85/4.99      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4451,plain,
% 35.85/4.99      ( k2_yellow_0(sK2,sK6(X0)) = X0
% 35.85/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_4288,c_3934]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4981,plain,
% 35.85/4.99      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 35.85/4.99      | r1_lattice3(sK2,sK4,X0) = iProver_top
% 35.85/4.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3910,c_4451]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_6012,plain,
% 35.85/4.99      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 35.85/4.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 35.85/4.99      inference(superposition,[status(thm)],[c_3935,c_4981]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4432,plain,
% 35.85/4.99      ( sK5 = sK5 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3184]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_30,negated_conjecture,
% 35.85/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(X0,sK4) ),
% 35.85/4.99      inference(cnf_transformation,[],[f84]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4421,plain,
% 35.85/4.99      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 35.85/4.99      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_30]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_29,negated_conjecture,
% 35.85/4.99      ( r2_yellow_0(sK2,sK6(X0))
% 35.85/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(X0,sK4) ),
% 35.85/4.99      inference(cnf_transformation,[],[f85]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4422,plain,
% 35.85/4.99      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 35.85/4.99      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_29]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4145,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5)
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 35.85/4.99      | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4087]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4142,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5)
% 35.85/4.99      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4094]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_4133,plain,
% 35.85/4.99      ( r1_lattice3(sK2,sK4,sK5)
% 35.85/4.99      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 35.85/4.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_4044]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3209,plain,
% 35.85/4.99      ( sK2 = sK2 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3184]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3190,plain,
% 35.85/4.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 35.85/4.99      theory(equality) ).
% 35.85/4.99  
% 35.85/4.99  cnf(c_3201,plain,
% 35.85/4.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 35.85/4.99      inference(instantiation,[status(thm)],[c_3190]) ).
% 35.85/4.99  
% 35.85/4.99  cnf(contradiction,plain,
% 35.85/4.99      ( $false ),
% 35.85/4.99      inference(minisat,
% 35.85/4.99                [status(thm)],
% 35.85/4.99                [c_83834,c_67051,c_64542,c_61588,c_60438,c_60408,c_59818,
% 35.85/4.99                 c_48844,c_48840,c_27476,c_20571,c_8148,c_6012,c_4432,
% 35.85/4.99                 c_4421,c_4422,c_4145,c_4142,c_4133,c_3209,c_3201,c_65,
% 35.85/4.99                 c_24,c_63,c_26]) ).
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.85/4.99  
% 35.85/4.99  ------                               Statistics
% 35.85/4.99  
% 35.85/4.99  ------ General
% 35.85/4.99  
% 35.85/4.99  abstr_ref_over_cycles:                  0
% 35.85/4.99  abstr_ref_under_cycles:                 0
% 35.85/4.99  gc_basic_clause_elim:                   0
% 35.85/4.99  forced_gc_time:                         0
% 35.85/4.99  parsing_time:                           0.012
% 35.85/4.99  unif_index_cands_time:                  0.
% 35.85/4.99  unif_index_add_time:                    0.
% 35.85/4.99  orderings_time:                         0.
% 35.85/4.99  out_proof_time:                         0.025
% 35.85/4.99  total_time:                             4.473
% 35.85/4.99  num_of_symbols:                         58
% 35.85/4.99  num_of_terms:                           52820
% 35.85/4.99  
% 35.85/4.99  ------ Preprocessing
% 35.85/4.99  
% 35.85/4.99  num_of_splits:                          2
% 35.85/4.99  num_of_split_atoms:                     2
% 35.85/4.99  num_of_reused_defs:                     0
% 35.85/4.99  num_eq_ax_congr_red:                    28
% 35.85/4.99  num_of_sem_filtered_clauses:            3
% 35.85/4.99  num_of_subtypes:                        0
% 35.85/4.99  monotx_restored_types:                  0
% 35.85/4.99  sat_num_of_epr_types:                   0
% 35.85/4.99  sat_num_of_non_cyclic_types:            0
% 35.85/4.99  sat_guarded_non_collapsed_types:        0
% 35.85/4.99  num_pure_diseq_elim:                    0
% 35.85/4.99  simp_replaced_by:                       0
% 35.85/4.99  res_preprocessed:                       161
% 35.85/4.99  prep_upred:                             0
% 35.85/4.99  prep_unflattend:                        146
% 35.85/4.99  smt_new_axioms:                         0
% 35.85/4.99  pred_elim_cands:                        6
% 35.85/4.99  pred_elim:                              7
% 35.85/4.99  pred_elim_cl:                           8
% 35.85/4.99  pred_elim_cycles:                       11
% 35.85/4.99  merged_defs:                            8
% 35.85/4.99  merged_defs_ncl:                        0
% 35.85/4.99  bin_hyper_res:                          8
% 35.85/4.99  prep_cycles:                            4
% 35.85/4.99  pred_elim_time:                         0.046
% 35.85/4.99  splitting_time:                         0.
% 35.85/4.99  sem_filter_time:                        0.
% 35.85/4.99  monotx_time:                            0.
% 35.85/4.99  subtype_inf_time:                       0.
% 35.85/4.99  
% 35.85/4.99  ------ Problem properties
% 35.85/4.99  
% 35.85/4.99  clauses:                                33
% 35.85/4.99  conjectures:                            8
% 35.85/4.99  epr:                                    3
% 35.85/4.99  horn:                                   24
% 35.85/4.99  ground:                                 6
% 35.85/4.99  unary:                                  4
% 35.85/4.99  binary:                                 5
% 35.85/4.99  lits:                                   105
% 35.85/4.99  lits_eq:                                8
% 35.85/4.99  fd_pure:                                0
% 35.85/4.99  fd_pseudo:                              0
% 35.85/4.99  fd_cond:                                0
% 35.85/4.99  fd_pseudo_cond:                         3
% 35.85/4.99  ac_symbols:                             0
% 35.85/4.99  
% 35.85/4.99  ------ Propositional Solver
% 35.85/4.99  
% 35.85/4.99  prop_solver_calls:                      50
% 35.85/4.99  prop_fast_solver_calls:                 8134
% 35.85/4.99  smt_solver_calls:                       0
% 35.85/4.99  smt_fast_solver_calls:                  0
% 35.85/4.99  prop_num_of_clauses:                    41559
% 35.85/4.99  prop_preprocess_simplified:             56354
% 35.85/4.99  prop_fo_subsumed:                       465
% 35.85/4.99  prop_solver_time:                       0.
% 35.85/4.99  smt_solver_time:                        0.
% 35.85/4.99  smt_fast_solver_time:                   0.
% 35.85/4.99  prop_fast_solver_time:                  0.
% 35.85/4.99  prop_unsat_core_time:                   0.003
% 35.85/4.99  
% 35.85/4.99  ------ QBF
% 35.85/4.99  
% 35.85/4.99  qbf_q_res:                              0
% 35.85/4.99  qbf_num_tautologies:                    0
% 35.85/4.99  qbf_prep_cycles:                        0
% 35.85/4.99  
% 35.85/4.99  ------ BMC1
% 35.85/4.99  
% 35.85/4.99  bmc1_current_bound:                     -1
% 35.85/4.99  bmc1_last_solved_bound:                 -1
% 35.85/4.99  bmc1_unsat_core_size:                   -1
% 35.85/4.99  bmc1_unsat_core_parents_size:           -1
% 35.85/4.99  bmc1_merge_next_fun:                    0
% 35.85/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.85/4.99  
% 35.85/4.99  ------ Instantiation
% 35.85/4.99  
% 35.85/4.99  inst_num_of_clauses:                    2600
% 35.85/4.99  inst_num_in_passive:                    895
% 35.85/4.99  inst_num_in_active:                     3441
% 35.85/4.99  inst_num_in_unprocessed:                682
% 35.85/4.99  inst_num_of_loops:                      4185
% 35.85/4.99  inst_num_of_learning_restarts:          1
% 35.85/4.99  inst_num_moves_active_passive:          731
% 35.85/4.99  inst_lit_activity:                      0
% 35.85/4.99  inst_lit_activity_moves:                2
% 35.85/4.99  inst_num_tautologies:                   0
% 35.85/4.99  inst_num_prop_implied:                  0
% 35.85/4.99  inst_num_existing_simplified:           0
% 35.85/4.99  inst_num_eq_res_simplified:             0
% 35.85/4.99  inst_num_child_elim:                    0
% 35.85/4.99  inst_num_of_dismatching_blockings:      3981
% 35.85/4.99  inst_num_of_non_proper_insts:           9399
% 35.85/4.99  inst_num_of_duplicates:                 0
% 35.85/4.99  inst_inst_num_from_inst_to_res:         0
% 35.85/4.99  inst_dismatching_checking_time:         0.
% 35.85/4.99  
% 35.85/4.99  ------ Resolution
% 35.85/4.99  
% 35.85/4.99  res_num_of_clauses:                     44
% 35.85/4.99  res_num_in_passive:                     44
% 35.85/4.99  res_num_in_active:                      0
% 35.85/4.99  res_num_of_loops:                       165
% 35.85/4.99  res_forward_subset_subsumed:            509
% 35.85/4.99  res_backward_subset_subsumed:           0
% 35.85/4.99  res_forward_subsumed:                   1
% 35.85/4.99  res_backward_subsumed:                  0
% 35.85/4.99  res_forward_subsumption_resolution:     3
% 35.85/4.99  res_backward_subsumption_resolution:    0
% 35.85/4.99  res_clause_to_clause_subsumption:       66577
% 35.85/4.99  res_orphan_elimination:                 0
% 35.85/4.99  res_tautology_del:                      862
% 35.85/4.99  res_num_eq_res_simplified:              0
% 35.85/4.99  res_num_sel_changes:                    0
% 35.85/4.99  res_moves_from_active_to_pass:          0
% 35.85/4.99  
% 35.85/4.99  ------ Superposition
% 35.85/4.99  
% 35.85/4.99  sup_time_total:                         0.
% 35.85/4.99  sup_time_generating:                    0.
% 35.85/4.99  sup_time_sim_full:                      0.
% 35.85/4.99  sup_time_sim_immed:                     0.
% 35.85/4.99  
% 35.85/4.99  sup_num_of_clauses:                     5734
% 35.85/4.99  sup_num_in_active:                      576
% 35.85/4.99  sup_num_in_passive:                     5158
% 35.85/4.99  sup_num_of_loops:                       836
% 35.85/4.99  sup_fw_superposition:                   6122
% 35.85/4.99  sup_bw_superposition:                   7167
% 35.85/4.99  sup_immediate_simplified:               5188
% 35.85/4.99  sup_given_eliminated:                   54
% 35.85/4.99  comparisons_done:                       0
% 35.85/4.99  comparisons_avoided:                    560
% 35.85/4.99  
% 35.85/4.99  ------ Simplifications
% 35.85/4.99  
% 35.85/4.99  
% 35.85/4.99  sim_fw_subset_subsumed:                 1566
% 35.85/4.99  sim_bw_subset_subsumed:                 596
% 35.85/4.99  sim_fw_subsumed:                        2630
% 35.85/4.99  sim_bw_subsumed:                        1256
% 35.85/4.99  sim_fw_subsumption_res:                 0
% 35.85/4.99  sim_bw_subsumption_res:                 0
% 35.85/4.99  sim_tautology_del:                      237
% 35.85/4.99  sim_eq_tautology_del:                   19
% 35.85/4.99  sim_eq_res_simp:                        1
% 35.85/4.99  sim_fw_demodulated:                     11
% 35.85/4.99  sim_bw_demodulated:                     14
% 35.85/4.99  sim_light_normalised:                   96
% 35.85/4.99  sim_joinable_taut:                      0
% 35.85/4.99  sim_joinable_simp:                      0
% 35.85/4.99  sim_ac_normalised:                      0
% 35.85/4.99  sim_smt_subsumption:                    0
% 35.85/4.99  
%------------------------------------------------------------------------------
