%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1679+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:10 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 643 expanded)
%              Number of clauses        :  135 ( 155 expanded)
%              Number of leaves         :   17 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          : 1361 (10139 expanded)
%              Number of equality atoms :  228 (1898 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   44 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f7,plain,(
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
    inference(rectify,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r1_lattice3(X0,X1,X7)
                      | ~ r1_lattice3(X0,X2,X7) )
                    & ( r1_lattice3(X0,X2,X7)
                      | ~ r1_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k2_yellow_0(X0,X5) != X4
              | ~ r2_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( k2_yellow_0(X0,X5) != sK5(X0,X1,X2)
            | ~ r2_yellow_0(X0,X5)
            | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X5) )
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ( ! [X5] :
                    ( k2_yellow_0(X0,X5) != sK5(X0,X1,X2)
                    | ~ r2_yellow_0(X0,X5)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X5) )
                & r2_hidden(sK5(X0,X1,X2),X2)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK5(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_yellow_0(X0,X1)
                  & ! [X3] :
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
               => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
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
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
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
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
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
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
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
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( k2_yellow_0(X0,X5) = X4
          & r2_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
     => ( k2_yellow_0(X0,sK9(X4)) = X4
        & r2_yellow_0(X0,sK9(X4))
        & m1_subset_1(sK9(X4),k1_zfmisc_1(X1))
        & v1_finset_1(sK9(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
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
     => ( k2_yellow_0(X0,sK8) != k2_yellow_0(X0,X1)
        & r2_yellow_0(X0,X1)
        & ! [X3] :
            ( r2_hidden(k2_yellow_0(X0,X3),sK8)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k2_yellow_0(X0,X5) = X4
                & r2_yellow_0(X0,X5)
                & m1_subset_1(X5,k1_zfmisc_1(X1))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,sK8)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & ! [X6] :
            ( r2_yellow_0(X0,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
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
     => ( ? [X2] :
            ( k2_yellow_0(X0,sK7) != k2_yellow_0(X0,X2)
            & r2_yellow_0(X0,sK7)
            & ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k2_yellow_0(X0,X5) = X4
                    & r2_yellow_0(X0,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(sK7))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & ! [X6] :
                ( r2_yellow_0(X0,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
                & r2_yellow_0(X0,X1)
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK6,X1) != k2_yellow_0(sK6,X2)
              & r2_yellow_0(sK6,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(sK6,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(sK6,X5) = X4
                      & r2_yellow_0(sK6,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
              & ! [X6] :
                  ( r2_yellow_0(sK6,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,sK8)
    & r2_yellow_0(sK6,sK7)
    & ! [X3] :
        ( r2_hidden(k2_yellow_0(sK6,X3),sK8)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k2_yellow_0(sK6,sK9(X4)) = X4
          & r2_yellow_0(sK6,sK9(X4))
          & m1_subset_1(sK9(X4),k1_zfmisc_1(sK7))
          & v1_finset_1(sK9(X4)) )
        | ~ r2_hidden(X4,sK8)
        | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
    & ! [X6] :
        ( r2_yellow_0(sK6,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f39,f38,f37,f36])).

fof(f62,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK5(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_yellow_0(X0,sK4(X0,X1))
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK4(X0,X1))
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X6] :
      ( r2_yellow_0(sK6,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X6] :
      ( r2_yellow_0(sK6,X6)
      | o_0_0_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X6) ) ),
    inference(definition_unfolding,[],[f66,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != sK4(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X4] :
      ( k2_yellow_0(sK6,sK9(X4)) = X4
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X4] :
      ( r2_yellow_0(sK6,sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X4] :
      ( m1_subset_1(sK9(X4),k1_zfmisc_1(sK7))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X4] :
      ( v1_finset_1(sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0)
        & k1_xboole_0 != sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0)
        & k1_xboole_0 != sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK6,X3),sK8)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK6,X3),sK8)
      | o_0_0_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X3) ) ),
    inference(definition_unfolding,[],[f71,f41])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK3(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != sK3(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    r2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k2_yellow_0(X1,X4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_403,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k2_yellow_0(X1,X4)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_404,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X1,X2)
    | r1_lattice3(sK6,X0,X2)
    | sP0(sK6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3)
    | ~ v3_orders_2(sK6)
    | ~ v1_finset_1(X3)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_406,plain,
    ( ~ r2_yellow_0(sK6,X3)
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sP0(sK6,X1)
    | r1_lattice3(sK6,X0,X2)
    | ~ r1_lattice3(sK6,X1,X2)
    | sP1(X0,sK6,X1)
    | ~ v1_finset_1(X3)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_31,c_30,c_28])).

cnf(c_407,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X1,X2)
    | r1_lattice3(sK6,X0,X2)
    | sP0(sK6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3)
    | ~ v1_finset_1(X3)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_7342,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,X2_52)
    | r1_lattice3(sK6,X0_52,X2_52)
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3_52)
    | ~ v1_finset_1(X3_52)
    | sK5(sK6,X1_52,X0_52) != k2_yellow_0(sK6,X3_52) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_9151,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,X2_52)
    | r1_lattice3(sK6,X0_52,X2_52)
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(X1_52))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,X1_52,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_7342])).

cnf(c_9625,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,X1_52)
    | ~ r1_lattice3(sK6,sK7,X1_52)
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_9151])).

cnf(c_14101,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_9625])).

cnf(c_14108,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_14101])).

cnf(c_12,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X0,X3)
    | r1_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k2_yellow_0(X1,X4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_508,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X0,X3)
    | r1_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k2_yellow_0(X1,X4)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_509,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X0,X2)
    | r1_lattice3(sK6,X1,X2)
    | sP0(sK6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3)
    | ~ v3_orders_2(sK6)
    | ~ v1_finset_1(X3)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_511,plain,
    ( ~ r2_yellow_0(sK6,X3)
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sP0(sK6,X1)
    | r1_lattice3(sK6,X1,X2)
    | ~ r1_lattice3(sK6,X0,X2)
    | sP1(X0,sK6,X1)
    | ~ v1_finset_1(X3)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_31,c_30,c_28])).

cnf(c_512,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X0,X2)
    | r1_lattice3(sK6,X1,X2)
    | sP0(sK6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3)
    | ~ v1_finset_1(X3)
    | sK5(sK6,X1,X0) != k2_yellow_0(sK6,X3) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_7339,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,X2_52)
    | r1_lattice3(sK6,X1_52,X2_52)
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X3_52)
    | ~ v1_finset_1(X3_52)
    | sK5(sK6,X1_52,X0_52) != k2_yellow_0(sK6,X3_52) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_9152,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,X2_52)
    | r1_lattice3(sK6,X1_52,X2_52)
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(X1_52))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,X1_52,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_7339])).

cnf(c_9631,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,X1_52)
    | r1_lattice3(sK6,sK7,X1_52)
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_9152])).

cnf(c_11574,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_9631])).

cnf(c_11576,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_11574])).

cnf(c_7366,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_8499,plain,
    ( X0_52 != X1_52
    | X0_52 = k2_yellow_0(sK6,X2_52)
    | k2_yellow_0(sK6,X2_52) != X1_52 ),
    inference(instantiation,[status(thm)],[c_7366])).

cnf(c_9129,plain,
    ( X0_52 != sK5(sK6,sK7,sK8)
    | X0_52 = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) != sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_8499])).

cnf(c_9909,plain,
    ( sK5(sK6,sK7,sK8) != sK5(sK6,sK7,sK8)
    | sK5(sK6,sK7,sK8) = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) != sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_9129])).

cnf(c_7365,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_9309,plain,
    ( sK5(sK6,sK7,X0_52) = sK5(sK6,sK7,X0_52) ),
    inference(instantiation,[status(thm)],[c_7365])).

cnf(c_9312,plain,
    ( sK5(sK6,sK7,sK8) = sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_9309])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7363,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | m1_subset_1(X0_52,X2_52)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X2_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9061,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | m1_subset_1(sK5(sK6,sK7,X0_52),X1_52) ),
    inference(instantiation,[status(thm)],[c_7363])).

cnf(c_9290,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_9061])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7356,plain,
    ( ~ sP0(X0_51,X0_52)
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_7885,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7356])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | r2_yellow_0(sK6,X0)
    | ~ v1_finset_1(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7347,negated_conjecture,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | r2_yellow_0(sK6,X0_52)
    | ~ v1_finset_1(X0_52)
    | o_0_0_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_7893,plain,
    ( o_0_0_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7347])).

cnf(c_8739,plain,
    ( sK4(X0_51,sK7) = o_0_0_xboole_0
    | sP0(X0_51,sK7) != iProver_top
    | r2_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top
    | v1_finset_1(sK4(X0_51,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7885,c_7893])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1)
    | v1_finset_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7355,plain,
    ( ~ sP0(X0_51,X0_52)
    | v1_finset_1(sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_7886,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | v1_finset_1(sK4(X0_51,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7355])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1)
    | sK4(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7357,plain,
    ( ~ sP0(X0_51,X0_52)
    | sK4(X0_51,X0_52) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_7884,plain,
    ( sK4(X0_51,X0_52) != o_0_0_xboole_0
    | sP0(X0_51,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7357])).

cnf(c_9077,plain,
    ( sP0(X0_51,sK7) != iProver_top
    | r2_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8739,c_7886,c_7884])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_yellow_0(X0,sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7358,plain,
    ( ~ sP0(X0_51,X0_52)
    | ~ r2_yellow_0(X0_51,sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7883,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,sK4(X0_51,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7358])).

cnf(c_9081,plain,
    ( sP0(sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_9077,c_7883])).

cnf(c_9082,plain,
    ( ~ sP0(sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9081])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k2_yellow_0(sK6,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7351,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | k2_yellow_0(sK6,sK9(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_9046,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_7351])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7350,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_9047,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_7350])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0),k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7349,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0_52),k1_zfmisc_1(sK7)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_9048,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_7349])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7348,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_9049,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | v1_finset_1(sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_7348])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_371,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_372,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X1,X2)
    | r1_lattice3(sK6,X0,X2)
    | sP0(sK6,X1)
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | sP0(sK6,X1)
    | r1_lattice3(sK6,X0,X2)
    | ~ r1_lattice3(sK6,X1,X2)
    | sP1(X0,sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_31,c_30,c_28])).

cnf(c_375,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X1,X2)
    | r1_lattice3(sK6,X0,X2)
    | sP0(sK6,X1)
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_7343,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,X2_52)
    | r1_lattice3(sK6,X0_52,X2_52)
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_8580,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X2_52))
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X2_52))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X2_52),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7343])).

cnf(c_8933,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8580])).

cnf(c_8935,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8933])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7360,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7881,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7360])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK6,X0),sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7352,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK6,X0_52),sK8)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0_52)
    | o_0_0_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_7888,plain,
    ( o_0_0_xboole_0 = X0_52
    | r2_hidden(k2_yellow_0(sK6,X0_52),sK8) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7352])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7362,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | ~ r2_hidden(k2_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_7879,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | r2_hidden(k2_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7362])).

cnf(c_8666,plain,
    ( sK3(sK8,sK6,X0_52) = o_0_0_xboole_0
    | sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(sK3(sK8,sK6,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7888,c_7879])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2)
    | v1_finset_1(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7359,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_7882,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7359])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | sK3(X0,X1,X2) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7361,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | sK3(X0_52,X0_51,X1_52) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7880,plain,
    ( sK3(X0_52,X0_51,X1_52) != o_0_0_xboole_0
    | sP1(X0_52,X0_51,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7361])).

cnf(c_8868,plain,
    ( sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8666,c_7882,c_7880])).

cnf(c_8872,plain,
    ( sP1(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7881,c_8868])).

cnf(c_8873,plain,
    ( ~ sP1(sK8,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8872])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X0,X3)
    | r1_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_476,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X0,X3)
    | r1_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_477,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X0,X2)
    | r1_lattice3(sK6,X1,X2)
    | sP0(sK6,X1)
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | sP0(sK6,X1)
    | r1_lattice3(sK6,X1,X2)
    | ~ r1_lattice3(sK6,X0,X2)
    | sP1(X0,sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_31,c_30,c_28])).

cnf(c_480,plain,
    ( sP1(X0,sK6,X1)
    | ~ r1_lattice3(sK6,X0,X2)
    | r1_lattice3(sK6,X1,X2)
    | sP0(sK6,X1)
    | r2_hidden(sK5(sK6,X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_7340,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,X2_52)
    | r1_lattice3(sK6,X1_52,X2_52)
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_8581,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X2_52))
    | r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X2_52))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X2_52),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7340])).

cnf(c_8710,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8581])).

cnf(c_8712,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8710])).

cnf(c_2,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_587,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_588,plain,
    ( m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0)
    | v2_struct_0(sK6)
    | k2_yellow_0(sK6,X1) = k2_yellow_0(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_592,plain,
    ( ~ r2_yellow_0(sK6,X0)
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6))
    | k2_yellow_0(sK6,X1) = k2_yellow_0(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_588,c_31])).

cnf(c_593,plain,
    ( m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X1) = k2_yellow_0(sK6,X0) ),
    inference(renaming,[status(thm)],[c_592])).

cnf(c_7338,plain,
    ( m1_subset_1(sK2(sK6,X0_52,X1_52),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,X1_52) = k2_yellow_0(sK6,X0_52) ),
    inference(subtyping,[status(esa)],[c_593])).

cnf(c_8369,plain,
    ( m1_subset_1(sK2(sK6,X0_52,sK8),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,sK8) = k2_yellow_0(sK6,X0_52) ),
    inference(instantiation,[status(thm)],[c_7338])).

cnf(c_8491,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK6,sK8) = k2_yellow_0(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_8369])).

cnf(c_8349,plain,
    ( k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_7365])).

cnf(c_8210,plain,
    ( k2_yellow_0(sK6,sK8) != X0_52
    | k2_yellow_0(sK6,sK7) != X0_52
    | k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_7366])).

cnf(c_8256,plain,
    ( k2_yellow_0(sK6,sK8) != k2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_8210])).

cnf(c_8348,plain,
    ( k2_yellow_0(sK6,sK8) != k2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK8)
    | k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_8256])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_608,plain,
    ( r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_609,plain,
    ( r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | ~ r2_yellow_0(sK6,X0)
    | v2_struct_0(sK6)
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( ~ r2_yellow_0(sK6,X0)
    | r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_31])).

cnf(c_614,plain,
    ( r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(renaming,[status(thm)],[c_613])).

cnf(c_7337,plain,
    ( r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,X1_52))
    | r1_lattice3(sK6,X1_52,sK2(sK6,X0_52,X1_52))
    | ~ r2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,X0_52) = k2_yellow_0(sK6,X1_52) ),
    inference(subtyping,[status(esa)],[c_614])).

cnf(c_8189,plain,
    ( r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_7337])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_632,plain,
    ( ~ r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_633,plain,
    ( ~ r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | ~ r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | ~ r2_yellow_0(sK6,X0)
    | v2_struct_0(sK6)
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_637,plain,
    ( ~ r2_yellow_0(sK6,X0)
    | ~ r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | ~ r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_31])).

cnf(c_638,plain,
    ( ~ r1_lattice3(sK6,X0,sK2(sK6,X0,X1))
    | ~ r1_lattice3(sK6,X1,sK2(sK6,X0,X1))
    | ~ r2_yellow_0(sK6,X0)
    | k2_yellow_0(sK6,X0) = k2_yellow_0(sK6,X1) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_7336,plain,
    ( ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,X1_52))
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,X0_52,X1_52))
    | ~ r2_yellow_0(sK6,X0_52)
    | k2_yellow_0(sK6,X0_52) = k2_yellow_0(sK6,X1_52) ),
    inference(subtyping,[status(esa)],[c_638])).

cnf(c_8186,plain,
    ( ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r2_yellow_0(sK6,sK7)
    | k2_yellow_0(sK6,sK7) = k2_yellow_0(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_7336])).

cnf(c_18,negated_conjecture,
    ( k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7354,negated_conjecture,
    ( k2_yellow_0(sK6,sK7) != k2_yellow_0(sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_19,negated_conjecture,
    ( r2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14108,c_11576,c_9909,c_9312,c_9290,c_9082,c_9046,c_9047,c_9048,c_9049,c_8935,c_8873,c_8712,c_8491,c_8349,c_8348,c_8189,c_8186,c_7354,c_19,c_26,c_27])).


%------------------------------------------------------------------------------
