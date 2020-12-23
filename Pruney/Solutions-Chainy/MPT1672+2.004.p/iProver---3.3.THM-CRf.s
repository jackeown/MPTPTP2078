%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:08 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  254 (4872 expanded)
%              Number of clauses        :  176 (1034 expanded)
%              Number of leaves         :   24 (1390 expanded)
%              Depth                    :   31
%              Number of atoms          : 1327 (82831 expanded)
%              Number of equality atoms :  374 (11226 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
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
    inference(pure_predicate_removal,[],[f14])).

fof(f26,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
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
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
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
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f84,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3938,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1069,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_1070,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_3913,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1054,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_1055,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_3914,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3944,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3942,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_523,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_524,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_3932,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_4585,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3942,c_3932])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_517,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_4648,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4585,c_517])).

cnf(c_4654,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_4648])).

cnf(c_19,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_916,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_917,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_3921,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r1_orders_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_16,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_970,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_971,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_3918,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_991,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_992,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_3917,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_20,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_900,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_901,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_3922,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_5359,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(X0),X1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3917,c_3922])).

cnf(c_9706,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3918,c_5359])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1012,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_1013,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_3916,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,sK1(sK2,X0,X1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_13221,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r2_lattice3(sK2,k1_tarski(X0),X0) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9706,c_3916])).

cnf(c_13226,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r1_orders_2(sK2,X0,X0) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3921,c_13221])).

cnf(c_9,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_599,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_37])).

cnf(c_600,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_604,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_38,c_36])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_620,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_37])).

cnf(c_621,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_625,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_38,c_36])).

cnf(c_683,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X2
    | X1 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_604,c_625])).

cnf(c_684,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_3126,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_684])).

cnf(c_3171,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3126])).

cnf(c_3125,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_684])).

cnf(c_3172,plain,
    ( r1_orders_2(sK2,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3125])).

cnf(c_3124,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_684])).

cnf(c_3929,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3124])).

cnf(c_5575,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3938,c_3929])).

cnf(c_13440,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13226,c_3171,c_3172,c_5575])).

cnf(c_13446,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4654,c_13440])).

cnf(c_13878,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
    | r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_13446])).

cnf(c_13957,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0))) = sK0(sK2,sK3,X0)
    | r2_lattice3(sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_13878])).

cnf(c_13962,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3938,c_13957])).

cnf(c_23,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_848,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_849,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_tarski(X2,X0) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_3925,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_4706,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3938,c_3925])).

cnf(c_14021,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13962,c_4706])).

cnf(c_14221,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14021,c_3922])).

cnf(c_62,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_64,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3135,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3147,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3135])).

cnf(c_3128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3155,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3128])).

cnf(c_4043,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_4134,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4043])).

cnf(c_4135,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4134])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1084,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_36])).

cnf(c_1085,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1084])).

cnf(c_4083,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_4137,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4083])).

cnf(c_4138,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4137])).

cnf(c_4077,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_4160,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_4077])).

cnf(c_4161,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4160])).

cnf(c_30,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4372,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4373,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4372])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4371,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4375,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4371])).

cnf(c_4701,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3128])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5092,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4618])).

cnf(c_5093,plain,
    ( m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5092])).

cnf(c_3133,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4048,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,u1_struct_0(sK2))
    | X2 != X0
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_4260,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(X1,u1_struct_0(sK2))
    | X1 != X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4048])).

cnf(c_4755,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | X0 != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4260])).

cnf(c_6195,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4755])).

cnf(c_6196,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6195])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3937,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4889,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
    | r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_3937])).

cnf(c_4991,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r2_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_4889])).

cnf(c_6392,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3938,c_4991])).

cnf(c_6454,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3128])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_949,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_950,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_4796,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_7481,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4796])).

cnf(c_7482,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) = iProver_top
    | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7481])).

cnf(c_3129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5664,plain,
    ( X0 != X1
    | sK0(sK2,sK4,sK5) != X1
    | sK0(sK2,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3129])).

cnf(c_6457,plain,
    ( X0 != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = X0
    | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5664])).

cnf(c_8322,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6457])).

cnf(c_4095,plain,
    ( ~ r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_6039,plain,
    ( ~ r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_4095])).

cnf(c_8928,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_6039])).

cnf(c_8929,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
    | r2_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8928])).

cnf(c_3134,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4145,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK2,X3,sK5)
    | X3 != X1
    | sK5 != X2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_4286,plain,
    ( ~ r1_orders_2(X0,X1,sK5)
    | r1_orders_2(sK2,X2,sK5)
    | X2 != X1
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_4145])).

cnf(c_9627,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | X0 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4286])).

cnf(c_15425,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_9627])).

cnf(c_15426,plain,
    ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15425])).

cnf(c_15532,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14221,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4373,c_4375,c_4701,c_5093,c_6196,c_6392,c_6454,c_7482,c_8322,c_8929,c_13962,c_15426])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_3931,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_15551,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_15532,c_3931])).

cnf(c_4177,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_4077])).

cnf(c_4184,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4177])).

cnf(c_4211,plain,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4473,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4211])).

cnf(c_4474,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4473])).

cnf(c_4024,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5349,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4024])).

cnf(c_5350,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5349])).

cnf(c_26,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3939,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4709,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_4706])).

cnf(c_4944,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4709,c_4706])).

cnf(c_5370,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4944])).

cnf(c_5372,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5370])).

cnf(c_10396,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5372,c_3922])).

cnf(c_10604,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10396,c_62])).

cnf(c_10605,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_10604])).

cnf(c_10612,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK3) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_10605])).

cnf(c_12106,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_10612])).

cnf(c_12380,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_12106])).

cnf(c_3912,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_12457,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12380,c_3912])).

cnf(c_12533,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12457,c_62])).

cnf(c_12539,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_12533])).

cnf(c_15647,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15551,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4184,c_4373,c_4375,c_4474,c_4701,c_5093,c_5350,c_6196,c_6392,c_6454,c_7482,c_8322,c_8929,c_12539,c_15426])).

cnf(c_15651,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15647,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4184,c_4373,c_4375,c_4474,c_4701,c_5093,c_5350,c_6196,c_6392,c_6454,c_7482,c_8322,c_8929,c_12539,c_15426,c_15551])).

cnf(c_15670,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_15651,c_517])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.63/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.50  
% 7.63/1.50  ------  iProver source info
% 7.63/1.50  
% 7.63/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.50  git: non_committed_changes: false
% 7.63/1.50  git: last_make_outside_of_git: false
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    ""
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             all
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         305.
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              default
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           true
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             true
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         true
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     num_symb
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       true
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     true
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.63/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_input_bw                          []
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  ------ Parsing...
% 7.63/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.50  ------ Proving...
% 7.63/1.50  ------ Problem Properties 
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  clauses                                 34
% 7.63/1.50  conjectures                             8
% 7.63/1.50  EPR                                     3
% 7.63/1.50  Horn                                    25
% 7.63/1.50  unary                                   4
% 7.63/1.50  binary                                  8
% 7.63/1.50  lits                                    103
% 7.63/1.50  lits eq                                 8
% 7.63/1.50  fd_pure                                 0
% 7.63/1.50  fd_pseudo                               0
% 7.63/1.50  fd_cond                                 0
% 7.63/1.50  fd_pseudo_cond                          3
% 7.63/1.50  AC symbols                              0
% 7.63/1.50  
% 7.63/1.50  ------ Schedule dynamic 5 is on 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  Current options:
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    ""
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             all
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         305.
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              default
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           true
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             true
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         true
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     none
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       false
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     true
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.63/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_input_bw                          []
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ Proving...
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS status Theorem for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50   Resolution empty clause
% 7.63/1.50  
% 7.63/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  fof(f12,conjecture,(
% 7.63/1.50    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f13,negated_conjecture,(
% 7.63/1.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 7.63/1.50    inference(negated_conjecture,[],[f12])).
% 7.63/1.50  
% 7.63/1.50  fof(f14,plain,(
% 7.63/1.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 7.63/1.50    inference(rectify,[],[f13])).
% 7.63/1.50  
% 7.63/1.50  fof(f15,plain,(
% 7.63/1.50    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 7.63/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.63/1.50  
% 7.63/1.50  fof(f26,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f15])).
% 7.63/1.50  
% 7.63/1.50  fof(f27,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.50    inference(flattening,[],[f26])).
% 7.63/1.50  
% 7.63/1.50  fof(f40,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.50    inference(nnf_transformation,[],[f27])).
% 7.63/1.50  
% 7.63/1.50  fof(f41,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.50    inference(flattening,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  fof(f42,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.50    inference(rectify,[],[f41])).
% 7.63/1.50  
% 7.63/1.50  fof(f47,plain,(
% 7.63/1.50    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f46,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f45,plain,(
% 7.63/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f44,plain,(
% 7.63/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f43,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f48,plain,(
% 7.63/1.50    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).
% 7.63/1.50  
% 7.63/1.50  fof(f85,plain,(
% 7.63/1.50    m1_subset_1(sK5,u1_struct_0(sK2))),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f8,axiom,(
% 7.63/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f20,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f8])).
% 7.63/1.50  
% 7.63/1.50  fof(f21,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(flattening,[],[f20])).
% 7.63/1.50  
% 7.63/1.50  fof(f31,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(nnf_transformation,[],[f21])).
% 7.63/1.50  
% 7.63/1.50  fof(f32,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(rectify,[],[f31])).
% 7.63/1.50  
% 7.63/1.50  fof(f33,plain,(
% 7.63/1.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f34,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.63/1.50  
% 7.63/1.50  fof(f61,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f34])).
% 7.63/1.50  
% 7.63/1.50  fof(f76,plain,(
% 7.63/1.50    l1_orders_2(sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f60,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f34])).
% 7.63/1.50  
% 7.63/1.50  fof(f3,axiom,(
% 7.63/1.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f28,plain,(
% 7.63/1.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.63/1.50    inference(nnf_transformation,[],[f3])).
% 7.63/1.50  
% 7.63/1.50  fof(f52,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f28])).
% 7.63/1.50  
% 7.63/1.50  fof(f4,axiom,(
% 7.63/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f29,plain,(
% 7.63/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.63/1.50    inference(nnf_transformation,[],[f4])).
% 7.63/1.50  
% 7.63/1.50  fof(f54,plain,(
% 7.63/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f29])).
% 7.63/1.50  
% 7.63/1.50  fof(f5,axiom,(
% 7.63/1.50    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f55,plain,(
% 7.63/1.50    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f5])).
% 7.63/1.50  
% 7.63/1.50  fof(f79,plain,(
% 7.63/1.50    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f1,axiom,(
% 7.63/1.50    v1_xboole_0(k1_xboole_0)),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f49,plain,(
% 7.63/1.50    v1_xboole_0(k1_xboole_0)),
% 7.63/1.50    inference(cnf_transformation,[],[f1])).
% 7.63/1.50  
% 7.63/1.50  fof(f2,axiom,(
% 7.63/1.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f50,plain,(
% 7.63/1.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f2])).
% 7.63/1.50  
% 7.63/1.50  fof(f10,axiom,(
% 7.63/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f24,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f10])).
% 7.63/1.50  
% 7.63/1.50  fof(f71,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f24])).
% 7.63/1.50  
% 7.63/1.50  fof(f9,axiom,(
% 7.63/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f22,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f9])).
% 7.63/1.50  
% 7.63/1.50  fof(f23,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(flattening,[],[f22])).
% 7.63/1.50  
% 7.63/1.50  fof(f35,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(nnf_transformation,[],[f23])).
% 7.63/1.50  
% 7.63/1.50  fof(f36,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(flattening,[],[f35])).
% 7.63/1.50  
% 7.63/1.50  fof(f37,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(rectify,[],[f36])).
% 7.63/1.50  
% 7.63/1.50  fof(f38,plain,(
% 7.63/1.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f39,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f65,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f39])).
% 7.63/1.50  
% 7.63/1.50  fof(f66,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f39])).
% 7.63/1.50  
% 7.63/1.50  fof(f70,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f24])).
% 7.63/1.50  
% 7.63/1.50  fof(f67,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f39])).
% 7.63/1.50  
% 7.63/1.50  fof(f7,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f18,plain,(
% 7.63/1.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f7])).
% 7.63/1.50  
% 7.63/1.50  fof(f19,plain,(
% 7.63/1.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.50    inference(flattening,[],[f18])).
% 7.63/1.50  
% 7.63/1.50  fof(f58,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f19])).
% 7.63/1.50  
% 7.63/1.50  fof(f75,plain,(
% 7.63/1.50    v3_orders_2(sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f74,plain,(
% 7.63/1.50    ~v2_struct_0(sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f6,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f16,plain,(
% 7.63/1.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f6])).
% 7.63/1.50  
% 7.63/1.50  fof(f17,plain,(
% 7.63/1.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.50    inference(flattening,[],[f16])).
% 7.63/1.50  
% 7.63/1.50  fof(f30,plain,(
% 7.63/1.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.50    inference(nnf_transformation,[],[f17])).
% 7.63/1.50  
% 7.63/1.50  fof(f56,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f30])).
% 7.63/1.50  
% 7.63/1.50  fof(f11,axiom,(
% 7.63/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 7.63/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f25,plain,(
% 7.63/1.50    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f11])).
% 7.63/1.50  
% 7.63/1.50  fof(f73,plain,(
% 7.63/1.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f25])).
% 7.63/1.50  
% 7.63/1.50  fof(f87,plain,(
% 7.63/1.50    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f62,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f34])).
% 7.63/1.50  
% 7.63/1.50  fof(f82,plain,(
% 7.63/1.50    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f81,plain,(
% 7.63/1.50    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f53,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f29])).
% 7.63/1.50  
% 7.63/1.50  fof(f83,plain,(
% 7.63/1.50    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f64,plain,(
% 7.63/1.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f39])).
% 7.63/1.50  
% 7.63/1.50  fof(f88,plain,(
% 7.63/1.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.50    inference(equality_resolution,[],[f64])).
% 7.63/1.50  
% 7.63/1.50  fof(f84,plain,(
% 7.63/1.50    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  fof(f86,plain,(
% 7.63/1.50    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 7.63/1.50    inference(cnf_transformation,[],[f48])).
% 7.63/1.50  
% 7.63/1.50  cnf(c_27,negated_conjecture,
% 7.63/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3938,plain,
% 7.63/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_11,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_36,negated_conjecture,
% 7.63/1.50      ( l1_orders_2(sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1069,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1070,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_1069]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3913,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1054,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1055,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_1054]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3914,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2,plain,
% 7.63/1.50      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3944,plain,
% 7.63/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3942,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.63/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6,plain,
% 7.63/1.50      ( v1_finset_1(k1_tarski(X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_33,negated_conjecture,
% 7.63/1.50      ( r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.63/1.50      | ~ v1_finset_1(X0)
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_523,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.63/1.50      | k1_tarski(X1) != X0
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_33]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_524,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,k1_tarski(X0))
% 7.63/1.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 7.63/1.50      | k1_xboole_0 = k1_tarski(X0) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_523]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3932,plain,
% 7.63/1.50      ( k1_xboole_0 = k1_tarski(X0)
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 7.63/1.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4585,plain,
% 7.63/1.50      ( k1_tarski(X0) = k1_xboole_0
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3942,c_3932]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_0,plain,
% 7.63/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1,plain,
% 7.63/1.50      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_517,plain,
% 7.63/1.50      ( k1_tarski(X0) != k1_xboole_0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4648,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,[status(thm)],[c_4585,c_517]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4654,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 7.63/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3944,c_4648]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_19,plain,
% 7.63/1.50      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 7.63/1.50      | ~ r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_916,plain,
% 7.63/1.50      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 7.63/1.50      | ~ r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_917,plain,
% 7.63/1.50      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 7.63/1.50      | ~ r1_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_916]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3921,plain,
% 7.63/1.50      ( r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X0,X1) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_16,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0)
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2 ),
% 7.63/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_970,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_971,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | ~ r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 7.63/1.50      | k1_yellow_0(sK2,X0) = X1 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_970]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3918,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,X0) = X1
% 7.63/1.50      | r2_lattice3(sK2,X0,X1) != iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,X0) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0)
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2 ),
% 7.63/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_991,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_992,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
% 7.63/1.50      | ~ r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | k1_yellow_0(sK2,X0) = X1 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_991]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3917,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,X0) = X1
% 7.63/1.50      | r2_lattice3(sK2,X0,X1) != iProver_top
% 7.63/1.50      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) = iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,X0) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_20,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 7.63/1.50      | r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_900,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 7.63/1.50      | r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_901,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 7.63/1.50      | r1_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_900]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3922,plain,
% 7.63/1.50      ( r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5359,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
% 7.63/1.50      | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK1(sK2,k1_tarski(X0),X1),u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3917,c_3922]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9706,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
% 7.63/1.50      | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3918,c_5359]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_14,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0)
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2 ),
% 7.63/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1012,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | k1_yellow_0(X0,X1) = X2
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1013,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
% 7.63/1.50      | ~ r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | k1_yellow_0(sK2,X0) = X1 ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_1012]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3916,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,X0) = X1
% 7.63/1.50      | r2_lattice3(sK2,X0,X1) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X1,sK1(sK2,X0,X1)) != iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,X0) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13221,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 7.63/1.50      | r2_lattice3(sK2,k1_tarski(X0),X0) != iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_9706,c_3916]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13226,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 7.63/1.50      | r1_orders_2(sK2,X0,X0) != iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3921,c_13221]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9,plain,
% 7.63/1.50      ( r3_orders_2(X0,X1,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | v2_struct_0(X0)
% 7.63/1.50      | ~ v3_orders_2(X0)
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_37,negated_conjecture,
% 7.63/1.50      ( v3_orders_2(sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_599,plain,
% 7.63/1.50      ( r3_orders_2(X0,X1,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | v2_struct_0(X0)
% 7.63/1.50      | ~ l1_orders_2(X0)
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_37]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_600,plain,
% 7.63/1.50      ( r3_orders_2(sK2,X0,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | v2_struct_0(sK2)
% 7.63/1.50      | ~ l1_orders_2(sK2) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_599]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_38,negated_conjecture,
% 7.63/1.50      ( ~ v2_struct_0(sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_604,plain,
% 7.63/1.50      ( r3_orders_2(sK2,X0,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_600,c_38,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8,plain,
% 7.63/1.50      ( r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ r3_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | v2_struct_0(X0)
% 7.63/1.50      | ~ v3_orders_2(X0)
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_620,plain,
% 7.63/1.50      ( r1_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ r3_orders_2(X0,X1,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.50      | v2_struct_0(X0)
% 7.63/1.50      | ~ l1_orders_2(X0)
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_37]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_621,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ r3_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | v2_struct_0(sK2)
% 7.63/1.50      | ~ l1_orders_2(sK2) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_620]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_625,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ r3_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_621,c_38,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_683,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | X0 != X2
% 7.63/1.50      | X1 != X2
% 7.63/1.50      | sK2 != sK2 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_604,c_625]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_684,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_683]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3126,plain,
% 7.63/1.50      ( sP1_iProver_split | sP0_iProver_split ),
% 7.63/1.50      inference(splitting,
% 7.63/1.50                [splitting(split),new_symbols(definition,[])],
% 7.63/1.50                [c_684]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3171,plain,
% 7.63/1.50      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3126]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3125,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X0)
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ sP1_iProver_split ),
% 7.63/1.50      inference(splitting,
% 7.63/1.50                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.63/1.50                [c_684]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3172,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,X0) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | sP1_iProver_split != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3125]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3124,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 7.63/1.50      inference(splitting,
% 7.63/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.63/1.50                [c_684]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3929,plain,
% 7.63/1.50      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | sP0_iProver_split != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3124]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5575,plain,
% 7.63/1.50      ( sP0_iProver_split != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3938,c_3929]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13440,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 7.63/1.50      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_13226,c_3171,c_3172,c_5575]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13446,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_4654,c_13440]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13878,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
% 7.63/1.50      | r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3914,c_13446]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13957,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0))) = sK0(sK2,sK3,X0)
% 7.63/1.50      | r2_lattice3(sK2,sK3,X0) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3913,c_13878]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13962,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 7.63/1.50      | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3938,c_13957]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r2_lattice3(X0,X3,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ r1_tarski(X3,X1)
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_848,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r2_lattice3(X0,X3,X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ r1_tarski(X3,X1)
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_849,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | r2_lattice3(sK2,X2,X1)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | ~ r1_tarski(X2,X0) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_848]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3925,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 7.63/1.50      | r2_lattice3(sK2,X2,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4706,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 7.63/1.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3938,c_3925]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_14021,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 7.63/1.50      | r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X0,sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_13962,c_4706]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_14221,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 7.63/1.50      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_14021,c_3922]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_62,plain,
% 7.63/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_25,negated_conjecture,
% 7.63/1.50      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 7.63/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_64,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 7.63/1.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3135,plain,
% 7.63/1.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.63/1.50      theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3147,plain,
% 7.63/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3135]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3128,plain,( X0 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3155,plain,
% 7.63/1.50      ( sK2 = sK2 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3128]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4043,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5)
% 7.63/1.50      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1055]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4134,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5)
% 7.63/1.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4043]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4135,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4134]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1084,plain,
% 7.63/1.50      ( r2_lattice3(X0,X1,X2)
% 7.63/1.50      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1085,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_1084]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4083,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5)
% 7.63/1.50      | ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1085]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4137,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5)
% 7.63/1.50      | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4083]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4138,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4137]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4077,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,sK5),X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_1070]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4160,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4077]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4161,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4160]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_30,negated_conjecture,
% 7.63/1.50      ( r1_yellow_0(sK2,sK6(X0))
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ r2_hidden(X0,sK4) ),
% 7.63/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4372,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.63/1.50      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_30]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4373,plain,
% 7.63/1.50      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
% 7.63/1.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4372]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_31,negated_conjecture,
% 7.63/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
% 7.63/1.50      | ~ r2_hidden(X0,sK4) ),
% 7.63/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4371,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 7.63/1.50      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4375,plain,
% 7.63/1.50      ( m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4371]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4701,plain,
% 7.63/1.50      ( sK5 = sK5 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3128]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4618,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5092,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 7.63/1.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4618]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5093,plain,
% 7.63/1.50      ( m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 7.63/1.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_5092]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3133,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.63/1.50      theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4048,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,X1)
% 7.63/1.50      | m1_subset_1(X2,u1_struct_0(sK2))
% 7.63/1.50      | X2 != X0
% 7.63/1.50      | u1_struct_0(sK2) != X1 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3133]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4260,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | X1 != X0
% 7.63/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4048]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4755,plain,
% 7.63/1.50      ( m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.63/1.50      | X0 != sK0(sK2,sK4,sK5)
% 7.63/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4260]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6195,plain,
% 7.63/1.50      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.63/1.50      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 7.63/1.50      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 7.63/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4755]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6196,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 7.63/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.63/1.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_6195]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_29,negated_conjecture,
% 7.63/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ r2_hidden(X0,sK4)
% 7.63/1.50      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3937,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,sK6(X0)) = X0
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4889,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
% 7.63/1.50      | r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3914,c_3937]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4991,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 7.63/1.50      | r2_lattice3(sK2,sK4,X0) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3913,c_4889]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6392,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 7.63/1.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3938,c_4991]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6454,plain,
% 7.63/1.50      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3128]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_17,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.63/1.50      | ~ l1_orders_2(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_949,plain,
% 7.63/1.50      ( ~ r2_lattice3(X0,X1,X2)
% 7.63/1.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.63/1.50      | ~ r1_yellow_0(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_950,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,X1)
% 7.63/1.50      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 7.63/1.50      | ~ r1_yellow_0(sK2,X0)
% 7.63/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_949]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4796,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 7.63/1.50      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
% 7.63/1.50      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_950]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7481,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 7.63/1.50      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 7.63/1.50      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4796]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7482,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) = iProver_top
% 7.63/1.50      | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
% 7.63/1.50      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_7481]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5664,plain,
% 7.63/1.50      ( X0 != X1 | sK0(sK2,sK4,sK5) != X1 | sK0(sK2,sK4,sK5) = X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3129]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6457,plain,
% 7.63/1.50      ( X0 != sK0(sK2,sK4,sK5)
% 7.63/1.50      | sK0(sK2,sK4,sK5) = X0
% 7.63/1.50      | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_5664]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8322,plain,
% 7.63/1.50      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 7.63/1.50      | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_6457]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4095,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,sK5)
% 7.63/1.50      | r2_lattice3(sK2,X1,sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | ~ r1_tarski(X1,X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_849]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6039,plain,
% 7.63/1.50      ( ~ r2_lattice3(sK2,X0,sK5)
% 7.63/1.50      | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4095]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8928,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 7.63/1.50      | ~ r2_lattice3(sK2,sK3,sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_6039]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8929,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
% 7.63/1.50      | r2_lattice3(sK2,sK3,sK5) != iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_8928]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3134,plain,
% 7.63/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.63/1.50      | r1_orders_2(X3,X4,X5)
% 7.63/1.50      | X3 != X0
% 7.63/1.50      | X4 != X1
% 7.63/1.50      | X5 != X2 ),
% 7.63/1.50      theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4145,plain,
% 7.63/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.63/1.50      | r1_orders_2(sK2,X3,sK5)
% 7.63/1.50      | X3 != X1
% 7.63/1.50      | sK5 != X2
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3134]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4286,plain,
% 7.63/1.50      ( ~ r1_orders_2(X0,X1,sK5)
% 7.63/1.50      | r1_orders_2(sK2,X2,sK5)
% 7.63/1.50      | X2 != X1
% 7.63/1.50      | sK5 != sK5
% 7.63/1.50      | sK2 != X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4145]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9627,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,sK5)
% 7.63/1.50      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 7.63/1.50      | X0 != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | sK5 != sK5
% 7.63/1.50      | sK2 != sK2 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4286]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15425,plain,
% 7.63/1.50      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 7.63/1.50      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 7.63/1.50      | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | sK5 != sK5
% 7.63/1.50      | sK2 != sK2 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_9627]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15426,plain,
% 7.63/1.50      ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.63/1.50      | sK5 != sK5
% 7.63/1.50      | sK2 != sK2
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_15425]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15532,plain,
% 7.63/1.50      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_14221,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4373,
% 7.63/1.50                 c_4375,c_4701,c_5093,c_6196,c_6392,c_6454,c_7482,c_8322,
% 7.63/1.50                 c_8929,c_13962,c_15426]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_28,negated_conjecture,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.63/1.50      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 7.63/1.50      | ~ v1_finset_1(X0)
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_538,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.63/1.50      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 7.63/1.50      | k1_tarski(X1) != X0
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_539,plain,
% 7.63/1.50      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 7.63/1.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 7.63/1.50      | k1_xboole_0 = k1_tarski(X0) ),
% 7.63/1.50      inference(unflattening,[status(thm)],[c_538]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3931,plain,
% 7.63/1.50      ( k1_xboole_0 = k1_tarski(X0)
% 7.63/1.50      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
% 7.63/1.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15551,plain,
% 7.63/1.50      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 7.63/1.50      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_15532,c_3931]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4177,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5)
% 7.63/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.63/1.50      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4077]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4184,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4177]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4211,plain,
% 7.63/1.50      ( ~ r2_hidden(X0,sK3) | r1_tarski(k1_tarski(X0),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4473,plain,
% 7.63/1.50      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4211]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4474,plain,
% 7.63/1.50      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4473]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4024,plain,
% 7.63/1.50      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 7.63/1.50      | ~ r1_tarski(k1_tarski(X0),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5349,plain,
% 7.63/1.50      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 7.63/1.50      | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4024]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5350,plain,
% 7.63/1.50      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_5349]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_26,negated_conjecture,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 7.63/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3939,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 7.63/1.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4709,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X0,sK3) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3939,c_4706]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4944,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X0,sK3) != iProver_top
% 7.63/1.50      | r1_tarski(X1,sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_4709,c_4706]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5370,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X0,sK3) != iProver_top
% 7.63/1.50      | r1_tarski(X0,sK4) != iProver_top
% 7.63/1.50      | iProver_top != iProver_top ),
% 7.63/1.50      inference(equality_factoring,[status(thm)],[c_4944]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5372,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(X0,sK3) != iProver_top
% 7.63/1.50      | r1_tarski(X0,sK4) != iProver_top ),
% 7.63/1.50      inference(equality_resolution_simp,[status(thm)],[c_5370]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10396,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_5372,c_3922]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10604,plain,
% 7.63/1.50      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,[status(thm)],[c_10396,c_62]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10605,plain,
% 7.63/1.50      ( r1_orders_2(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 7.63/1.50      inference(renaming,[status(thm)],[c_10604]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10612,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3914,c_10605]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12106,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top
% 7.63/1.50      | r1_tarski(k1_tarski(sK0(sK2,X0,X1)),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3944,c_10612]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12380,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,X0,X1),sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),sK3) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3944,c_12106]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3912,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 7.63/1.50      | r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12457,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_12380,c_3912]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12533,plain,
% 7.63/1.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,sK5),sK3) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,[status(thm)],[c_12457,c_62]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12539,plain,
% 7.63/1.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 7.63/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.63/1.50      | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3913,c_12533]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15647,plain,
% 7.63/1.50      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 7.63/1.50      | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_15551,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4184,
% 7.63/1.50                 c_4373,c_4375,c_4474,c_4701,c_5093,c_5350,c_6196,c_6392,
% 7.63/1.50                 c_6454,c_7482,c_8322,c_8929,c_12539,c_15426]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15651,plain,
% 7.63/1.50      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_15647,c_62,c_64,c_3147,c_3155,c_4135,c_4138,c_4161,c_4184,
% 7.63/1.50                 c_4373,c_4375,c_4474,c_4701,c_5093,c_5350,c_6196,c_6392,
% 7.63/1.50                 c_6454,c_7482,c_8322,c_8929,c_12539,c_15426,c_15551]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15670,plain,
% 7.63/1.50      ( $false ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_15651,c_517]) ).
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  ------                               Statistics
% 7.63/1.50  
% 7.63/1.50  ------ General
% 7.63/1.50  
% 7.63/1.50  abstr_ref_over_cycles:                  0
% 7.63/1.50  abstr_ref_under_cycles:                 0
% 7.63/1.50  gc_basic_clause_elim:                   0
% 7.63/1.50  forced_gc_time:                         0
% 7.63/1.50  parsing_time:                           0.012
% 7.63/1.50  unif_index_cands_time:                  0.
% 7.63/1.50  unif_index_add_time:                    0.
% 7.63/1.50  orderings_time:                         0.
% 7.63/1.50  out_proof_time:                         0.018
% 7.63/1.50  total_time:                             0.513
% 7.63/1.50  num_of_symbols:                         58
% 7.63/1.50  num_of_terms:                           9709
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing
% 7.63/1.50  
% 7.63/1.50  num_of_splits:                          2
% 7.63/1.50  num_of_split_atoms:                     2
% 7.63/1.50  num_of_reused_defs:                     0
% 7.63/1.50  num_eq_ax_congr_red:                    31
% 7.63/1.50  num_of_sem_filtered_clauses:            3
% 7.63/1.50  num_of_subtypes:                        0
% 7.63/1.50  monotx_restored_types:                  0
% 7.63/1.50  sat_num_of_epr_types:                   0
% 7.63/1.50  sat_num_of_non_cyclic_types:            0
% 7.63/1.50  sat_guarded_non_collapsed_types:        0
% 7.63/1.50  num_pure_diseq_elim:                    0
% 7.63/1.50  simp_replaced_by:                       0
% 7.63/1.50  res_preprocessed:                       166
% 7.63/1.50  prep_upred:                             0
% 7.63/1.50  prep_unflattend:                        146
% 7.63/1.50  smt_new_axioms:                         0
% 7.63/1.50  pred_elim_cands:                        7
% 7.63/1.50  pred_elim:                              6
% 7.63/1.50  pred_elim_cl:                           7
% 7.63/1.50  pred_elim_cycles:                       13
% 7.63/1.50  merged_defs:                            24
% 7.63/1.50  merged_defs_ncl:                        0
% 7.63/1.50  bin_hyper_res:                          24
% 7.63/1.50  prep_cycles:                            4
% 7.63/1.50  pred_elim_time:                         0.043
% 7.63/1.50  splitting_time:                         0.
% 7.63/1.50  sem_filter_time:                        0.
% 7.63/1.50  monotx_time:                            0.001
% 7.63/1.50  subtype_inf_time:                       0.
% 7.63/1.50  
% 7.63/1.50  ------ Problem properties
% 7.63/1.50  
% 7.63/1.50  clauses:                                34
% 7.63/1.50  conjectures:                            8
% 7.63/1.50  epr:                                    3
% 7.63/1.50  horn:                                   25
% 7.63/1.50  ground:                                 6
% 7.63/1.50  unary:                                  4
% 7.63/1.50  binary:                                 8
% 7.63/1.50  lits:                                   103
% 7.63/1.50  lits_eq:                                8
% 7.63/1.50  fd_pure:                                0
% 7.63/1.50  fd_pseudo:                              0
% 7.63/1.50  fd_cond:                                0
% 7.63/1.50  fd_pseudo_cond:                         3
% 7.63/1.50  ac_symbols:                             0
% 7.63/1.50  
% 7.63/1.50  ------ Propositional Solver
% 7.63/1.50  
% 7.63/1.50  prop_solver_calls:                      36
% 7.63/1.50  prop_fast_solver_calls:                 2974
% 7.63/1.50  smt_solver_calls:                       0
% 7.63/1.50  smt_fast_solver_calls:                  0
% 7.63/1.50  prop_num_of_clauses:                    6440
% 7.63/1.50  prop_preprocess_simplified:             14101
% 7.63/1.50  prop_fo_subsumed:                       112
% 7.63/1.50  prop_solver_time:                       0.
% 7.63/1.50  smt_solver_time:                        0.
% 7.63/1.50  smt_fast_solver_time:                   0.
% 7.63/1.50  prop_fast_solver_time:                  0.
% 7.63/1.50  prop_unsat_core_time:                   0.
% 7.63/1.50  
% 7.63/1.50  ------ QBF
% 7.63/1.50  
% 7.63/1.50  qbf_q_res:                              0
% 7.63/1.50  qbf_num_tautologies:                    0
% 7.63/1.50  qbf_prep_cycles:                        0
% 7.63/1.50  
% 7.63/1.50  ------ BMC1
% 7.63/1.50  
% 7.63/1.50  bmc1_current_bound:                     -1
% 7.63/1.50  bmc1_last_solved_bound:                 -1
% 7.63/1.50  bmc1_unsat_core_size:                   -1
% 7.63/1.50  bmc1_unsat_core_parents_size:           -1
% 7.63/1.50  bmc1_merge_next_fun:                    0
% 7.63/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation
% 7.63/1.50  
% 7.63/1.50  inst_num_of_clauses:                    1774
% 7.63/1.50  inst_num_in_passive:                    669
% 7.63/1.50  inst_num_in_active:                     961
% 7.63/1.50  inst_num_in_unprocessed:                144
% 7.63/1.50  inst_num_of_loops:                      1280
% 7.63/1.50  inst_num_of_learning_restarts:          0
% 7.63/1.50  inst_num_moves_active_passive:          312
% 7.63/1.50  inst_lit_activity:                      0
% 7.63/1.50  inst_lit_activity_moves:                1
% 7.63/1.50  inst_num_tautologies:                   0
% 7.63/1.50  inst_num_prop_implied:                  0
% 7.63/1.50  inst_num_existing_simplified:           0
% 7.63/1.50  inst_num_eq_res_simplified:             0
% 7.63/1.50  inst_num_child_elim:                    0
% 7.63/1.50  inst_num_of_dismatching_blockings:      453
% 7.63/1.50  inst_num_of_non_proper_insts:           2308
% 7.63/1.50  inst_num_of_duplicates:                 0
% 7.63/1.50  inst_inst_num_from_inst_to_res:         0
% 7.63/1.50  inst_dismatching_checking_time:         0.
% 7.63/1.50  
% 7.63/1.50  ------ Resolution
% 7.63/1.50  
% 7.63/1.50  res_num_of_clauses:                     0
% 7.63/1.50  res_num_in_passive:                     0
% 7.63/1.50  res_num_in_active:                      0
% 7.63/1.50  res_num_of_loops:                       170
% 7.63/1.50  res_forward_subset_subsumed:            158
% 7.63/1.50  res_backward_subset_subsumed:           0
% 7.63/1.50  res_forward_subsumed:                   1
% 7.63/1.50  res_backward_subsumed:                  0
% 7.63/1.50  res_forward_subsumption_resolution:     3
% 7.63/1.50  res_backward_subsumption_resolution:    0
% 7.63/1.50  res_clause_to_clause_subsumption:       3271
% 7.63/1.50  res_orphan_elimination:                 0
% 7.63/1.50  res_tautology_del:                      218
% 7.63/1.50  res_num_eq_res_simplified:              0
% 7.63/1.50  res_num_sel_changes:                    0
% 7.63/1.50  res_moves_from_active_to_pass:          0
% 7.63/1.50  
% 7.63/1.50  ------ Superposition
% 7.63/1.50  
% 7.63/1.50  sup_time_total:                         0.
% 7.63/1.50  sup_time_generating:                    0.
% 7.63/1.50  sup_time_sim_full:                      0.
% 7.63/1.50  sup_time_sim_immed:                     0.
% 7.63/1.50  
% 7.63/1.50  sup_num_of_clauses:                     341
% 7.63/1.50  sup_num_in_active:                      200
% 7.63/1.50  sup_num_in_passive:                     141
% 7.63/1.50  sup_num_of_loops:                       255
% 7.63/1.50  sup_fw_superposition:                   299
% 7.63/1.50  sup_bw_superposition:                   228
% 7.63/1.50  sup_immediate_simplified:               120
% 7.63/1.50  sup_given_eliminated:                   1
% 7.63/1.50  comparisons_done:                       0
% 7.63/1.50  comparisons_avoided:                    8
% 7.63/1.50  
% 7.63/1.50  ------ Simplifications
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  sim_fw_subset_subsumed:                 59
% 7.63/1.50  sim_bw_subset_subsumed:                 30
% 7.63/1.50  sim_fw_subsumed:                        50
% 7.63/1.50  sim_bw_subsumed:                        47
% 7.63/1.50  sim_fw_subsumption_res:                 0
% 7.63/1.50  sim_bw_subsumption_res:                 0
% 7.63/1.50  sim_tautology_del:                      7
% 7.63/1.50  sim_eq_tautology_del:                   0
% 7.63/1.50  sim_eq_res_simp:                        9
% 7.63/1.50  sim_fw_demodulated:                     0
% 7.63/1.50  sim_bw_demodulated:                     1
% 7.63/1.50  sim_light_normalised:                   5
% 7.63/1.50  sim_joinable_taut:                      0
% 7.63/1.50  sim_joinable_simp:                      0
% 7.63/1.50  sim_ac_normalised:                      0
% 7.63/1.50  sim_smt_subsumption:                    0
% 7.63/1.50  
%------------------------------------------------------------------------------
