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
% DateTime   : Thu Dec  3 12:21:07 EST 2020

% Result     : Theorem 31.77s
% Output     : CNFRefutation 31.77s
% Verified   : 
% Statistics : Number of formulae       :  250 (6202 expanded)
%              Number of clauses        :  174 (1372 expanded)
%              Number of leaves         :   21 (1655 expanded)
%              Depth                    :   35
%              Number of atoms          : 1291 (100985 expanded)
%              Number of equality atoms :  367 (14017 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

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
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).

fof(f84,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X3,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f81,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f80,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_26,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4137,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4136,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_833,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_834,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_tarski(X2,X0) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_4122,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_5068,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_4122])).

cnf(c_5073,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_5068])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4142,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_993,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_36])).

cnf(c_994,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_4113,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_5394,plain,
    ( r1_orders_2(sK2,sK5,X0) = iProver_top
    | r2_lattice3(sK2,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_4113])).

cnf(c_5455,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top
    | r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_5394])).

cnf(c_5464,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top
    | r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5073,c_5455])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_903,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_904,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_4118,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_5108,plain,
    ( r1_orders_2(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4118,c_5068])).

cnf(c_60,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5995,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_orders_2(sK2,X0,sK5) != iProver_top
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5108,c_60])).

cnf(c_5996,plain,
    ( r1_orders_2(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5995])).

cnf(c_6001,plain,
    ( r1_orders_2(sK2,sK5,sK5) != iProver_top
    | r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_5996])).

cnf(c_9381,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(X1,k1_tarski(sK5)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_6001])).

cnf(c_30529,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X1),sK5) = iProver_top
    | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4142,c_9381])).

cnf(c_25,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4138,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_32054,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_30529,c_4138])).

cnf(c_16,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_921,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_922,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_4117,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_227,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_228,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_805,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_228,c_36])).

cnf(c_806,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0))
    | ~ r1_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_4124,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_5069,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) != iProver_top
    | r2_lattice3(sK2,X2,k1_yellow_0(sK2,X1)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_4122])).

cnf(c_5962,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4124,c_5069])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_885,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_886,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_4119,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_5988,plain,
    ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5962,c_4119])).

cnf(c_10334,plain,
    ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_5988])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X1)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_546,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X1)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_547,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_lattice3(sK2,X2,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_36])).

cnf(c_550,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r2_lattice3(sK2,X2,X0)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_549])).

cnf(c_4129,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X0) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_5492,plain,
    ( r1_orders_2(sK2,sK5,X0) != iProver_top
    | r2_lattice3(sK2,X1,X0) = iProver_top
    | r2_lattice3(sK2,X1,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_4129])).

cnf(c_5502,plain,
    ( r1_orders_2(sK2,sK5,k1_yellow_0(sK2,X0)) != iProver_top
    | r2_lattice3(sK2,X1,k1_yellow_0(sK2,X0)) = iProver_top
    | r2_lattice3(sK2,X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_5492])).

cnf(c_10388,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10334,c_5502])).

cnf(c_71134,plain,
    ( r1_yellow_0(sK2,X1) != iProver_top
    | r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10388,c_60])).

cnf(c_71135,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_71134])).

cnf(c_71144,plain,
    ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_71135,c_4119])).

cnf(c_71999,plain,
    ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_71144])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1044,plain,
    ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_36])).

cnf(c_1045,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1044])).

cnf(c_4110,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
    | r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_72017,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_71999,c_4110])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1014,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_36])).

cnf(c_1015,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_4248,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1))
    | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_4249,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4248])).

cnf(c_72479,plain,
    ( r1_yellow_0(sK2,X1) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
    | r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72017,c_4249])).

cnf(c_72480,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_72479])).

cnf(c_72500,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_yellow_0(sK2,X1) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,k1_yellow_0(sK2,X1)),k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_tarski(k1_tarski(sK5),X1) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_32054,c_72480])).

cnf(c_62,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4243,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_4757,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4243])).

cnf(c_4758,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4757])).

cnf(c_4316,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
    | r2_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_4756,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4316])).

cnf(c_4760,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4756])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1029,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_36])).

cnf(c_1030,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1029])).

cnf(c_4303,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_4755,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_4303])).

cnf(c_4762,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4755])).

cnf(c_4501,plain,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5088,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4501])).

cnf(c_5089,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5088])).

cnf(c_4281,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | ~ r2_lattice3(sK2,k1_tarski(X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_5604,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4281])).

cnf(c_5613,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5604])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4224,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5806,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4224])).

cnf(c_5807,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5806])).

cnf(c_6,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_33,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_581,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_582,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_9033,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_9034,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9033])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_9032,plain,
    ( ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_9036,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9032])).

cnf(c_4363,plain,
    ( r1_orders_2(sK2,X0,sK5)
    | ~ r2_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_4478,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
    | ~ r2_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(k1_yellow_0(sK2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_4363])).

cnf(c_25066,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_4478])).

cnf(c_25067,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25066])).

cnf(c_25098,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_25099,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25098])).

cnf(c_44580,plain,
    ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_44581,plain,
    ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44580])).

cnf(c_4357,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ r2_lattice3(sK2,X2,k1_yellow_0(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_4607,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
    | ~ r2_lattice3(sK2,X1,k1_yellow_0(sK2,X0))
    | r2_lattice3(sK2,X1,sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4357])).

cnf(c_6422,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,X0))
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4607])).

cnf(c_44990,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6422])).

cnf(c_44997,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44990])).

cnf(c_3312,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13997,plain,
    ( X0 != X1
    | k1_tarski(X2) != X1
    | k1_tarski(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_3312])).

cnf(c_41590,plain,
    ( X0 != k1_tarski(X1)
    | k1_tarski(X1) = X0
    | k1_tarski(X1) != k1_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_13997])).

cnf(c_51427,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_41590])).

cnf(c_3311,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_63256,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_3311])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_517,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_70402,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_73068,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72500,c_60,c_62,c_4758,c_4760,c_4762,c_5089,c_5613,c_5807,c_9034,c_9036,c_25067,c_25099,c_44581,c_44997,c_51427,c_63256,c_70402])).

cnf(c_73074,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5073,c_73068])).

cnf(c_4111,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_4112,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4135,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5735,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
    | r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_4135])).

cnf(c_5851,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r2_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4111,c_5735])).

cnf(c_11110,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4136,c_5851])).

cnf(c_73072,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_11110,c_73068])).

cnf(c_14,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_235,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_234])).

cnf(c_787,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_36])).

cnf(c_788,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_4125,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1) = iProver_top
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_73204,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
    | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
    | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73072,c_4125])).

cnf(c_4420,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4243])).

cnf(c_4421,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4420])).

cnf(c_4460,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_4303])).

cnf(c_4461,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4460])).

cnf(c_30,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5146,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5147,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5146])).

cnf(c_74866,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73204,c_60,c_62,c_4421,c_4461,c_4758,c_4760,c_4762,c_5089,c_5147,c_5613,c_5807,c_9034,c_9036,c_25067,c_25099,c_44581,c_44997,c_51427,c_63256,c_70402])).

cnf(c_74867,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
    | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_74866])).

cnf(c_74878,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_73074,c_74867])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4133,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4548,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK6(X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4139])).

cnf(c_5020,plain,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4) != iProver_top
    | r1_tarski(sK6(k1_yellow_0(sK2,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_4548])).

cnf(c_73205,plain,
    ( r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_73072,c_5020])).

cnf(c_73436,plain,
    ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73205,c_73072])).

cnf(c_4423,plain,
    ( ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4316])).

cnf(c_4424,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4423])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74878,c_73436,c_73068,c_4461,c_4424,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.77/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.77/4.50  
% 31.77/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.77/4.50  
% 31.77/4.50  ------  iProver source info
% 31.77/4.50  
% 31.77/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.77/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.77/4.50  git: non_committed_changes: false
% 31.77/4.50  git: last_make_outside_of_git: false
% 31.77/4.50  
% 31.77/4.50  ------ 
% 31.77/4.50  
% 31.77/4.50  ------ Input Options
% 31.77/4.50  
% 31.77/4.50  --out_options                           all
% 31.77/4.50  --tptp_safe_out                         true
% 31.77/4.50  --problem_path                          ""
% 31.77/4.50  --include_path                          ""
% 31.77/4.50  --clausifier                            res/vclausify_rel
% 31.77/4.50  --clausifier_options                    ""
% 31.77/4.50  --stdin                                 false
% 31.77/4.50  --stats_out                             all
% 31.77/4.50  
% 31.77/4.50  ------ General Options
% 31.77/4.50  
% 31.77/4.50  --fof                                   false
% 31.77/4.50  --time_out_real                         305.
% 31.77/4.50  --time_out_virtual                      -1.
% 31.77/4.50  --symbol_type_check                     false
% 31.77/4.50  --clausify_out                          false
% 31.77/4.50  --sig_cnt_out                           false
% 31.77/4.50  --trig_cnt_out                          false
% 31.77/4.50  --trig_cnt_out_tolerance                1.
% 31.77/4.50  --trig_cnt_out_sk_spl                   false
% 31.77/4.50  --abstr_cl_out                          false
% 31.77/4.50  
% 31.77/4.50  ------ Global Options
% 31.77/4.50  
% 31.77/4.50  --schedule                              default
% 31.77/4.50  --add_important_lit                     false
% 31.77/4.50  --prop_solver_per_cl                    1000
% 31.77/4.50  --min_unsat_core                        false
% 31.77/4.50  --soft_assumptions                      false
% 31.77/4.50  --soft_lemma_size                       3
% 31.77/4.50  --prop_impl_unit_size                   0
% 31.77/4.50  --prop_impl_unit                        []
% 31.77/4.50  --share_sel_clauses                     true
% 31.77/4.50  --reset_solvers                         false
% 31.77/4.50  --bc_imp_inh                            [conj_cone]
% 31.77/4.50  --conj_cone_tolerance                   3.
% 31.77/4.50  --extra_neg_conj                        none
% 31.77/4.50  --large_theory_mode                     true
% 31.77/4.50  --prolific_symb_bound                   200
% 31.77/4.50  --lt_threshold                          2000
% 31.77/4.50  --clause_weak_htbl                      true
% 31.77/4.50  --gc_record_bc_elim                     false
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing Options
% 31.77/4.50  
% 31.77/4.50  --preprocessing_flag                    true
% 31.77/4.50  --time_out_prep_mult                    0.1
% 31.77/4.50  --splitting_mode                        input
% 31.77/4.50  --splitting_grd                         true
% 31.77/4.50  --splitting_cvd                         false
% 31.77/4.50  --splitting_cvd_svl                     false
% 31.77/4.50  --splitting_nvd                         32
% 31.77/4.50  --sub_typing                            true
% 31.77/4.50  --prep_gs_sim                           true
% 31.77/4.50  --prep_unflatten                        true
% 31.77/4.50  --prep_res_sim                          true
% 31.77/4.50  --prep_upred                            true
% 31.77/4.50  --prep_sem_filter                       exhaustive
% 31.77/4.50  --prep_sem_filter_out                   false
% 31.77/4.50  --pred_elim                             true
% 31.77/4.50  --res_sim_input                         true
% 31.77/4.50  --eq_ax_congr_red                       true
% 31.77/4.50  --pure_diseq_elim                       true
% 31.77/4.50  --brand_transform                       false
% 31.77/4.50  --non_eq_to_eq                          false
% 31.77/4.50  --prep_def_merge                        true
% 31.77/4.50  --prep_def_merge_prop_impl              false
% 31.77/4.50  --prep_def_merge_mbd                    true
% 31.77/4.50  --prep_def_merge_tr_red                 false
% 31.77/4.50  --prep_def_merge_tr_cl                  false
% 31.77/4.50  --smt_preprocessing                     true
% 31.77/4.50  --smt_ac_axioms                         fast
% 31.77/4.50  --preprocessed_out                      false
% 31.77/4.50  --preprocessed_stats                    false
% 31.77/4.50  
% 31.77/4.50  ------ Abstraction refinement Options
% 31.77/4.50  
% 31.77/4.50  --abstr_ref                             []
% 31.77/4.50  --abstr_ref_prep                        false
% 31.77/4.50  --abstr_ref_until_sat                   false
% 31.77/4.50  --abstr_ref_sig_restrict                funpre
% 31.77/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.50  --abstr_ref_under                       []
% 31.77/4.50  
% 31.77/4.50  ------ SAT Options
% 31.77/4.50  
% 31.77/4.50  --sat_mode                              false
% 31.77/4.50  --sat_fm_restart_options                ""
% 31.77/4.50  --sat_gr_def                            false
% 31.77/4.50  --sat_epr_types                         true
% 31.77/4.50  --sat_non_cyclic_types                  false
% 31.77/4.50  --sat_finite_models                     false
% 31.77/4.50  --sat_fm_lemmas                         false
% 31.77/4.50  --sat_fm_prep                           false
% 31.77/4.50  --sat_fm_uc_incr                        true
% 31.77/4.50  --sat_out_model                         small
% 31.77/4.50  --sat_out_clauses                       false
% 31.77/4.50  
% 31.77/4.50  ------ QBF Options
% 31.77/4.50  
% 31.77/4.50  --qbf_mode                              false
% 31.77/4.50  --qbf_elim_univ                         false
% 31.77/4.50  --qbf_dom_inst                          none
% 31.77/4.50  --qbf_dom_pre_inst                      false
% 31.77/4.50  --qbf_sk_in                             false
% 31.77/4.50  --qbf_pred_elim                         true
% 31.77/4.50  --qbf_split                             512
% 31.77/4.50  
% 31.77/4.50  ------ BMC1 Options
% 31.77/4.50  
% 31.77/4.50  --bmc1_incremental                      false
% 31.77/4.50  --bmc1_axioms                           reachable_all
% 31.77/4.50  --bmc1_min_bound                        0
% 31.77/4.50  --bmc1_max_bound                        -1
% 31.77/4.50  --bmc1_max_bound_default                -1
% 31.77/4.50  --bmc1_symbol_reachability              true
% 31.77/4.50  --bmc1_property_lemmas                  false
% 31.77/4.50  --bmc1_k_induction                      false
% 31.77/4.50  --bmc1_non_equiv_states                 false
% 31.77/4.50  --bmc1_deadlock                         false
% 31.77/4.50  --bmc1_ucm                              false
% 31.77/4.50  --bmc1_add_unsat_core                   none
% 31.77/4.50  --bmc1_unsat_core_children              false
% 31.77/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.50  --bmc1_out_stat                         full
% 31.77/4.50  --bmc1_ground_init                      false
% 31.77/4.50  --bmc1_pre_inst_next_state              false
% 31.77/4.50  --bmc1_pre_inst_state                   false
% 31.77/4.50  --bmc1_pre_inst_reach_state             false
% 31.77/4.50  --bmc1_out_unsat_core                   false
% 31.77/4.50  --bmc1_aig_witness_out                  false
% 31.77/4.50  --bmc1_verbose                          false
% 31.77/4.50  --bmc1_dump_clauses_tptp                false
% 31.77/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.50  --bmc1_dump_file                        -
% 31.77/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.50  --bmc1_ucm_extend_mode                  1
% 31.77/4.50  --bmc1_ucm_init_mode                    2
% 31.77/4.50  --bmc1_ucm_cone_mode                    none
% 31.77/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.50  --bmc1_ucm_relax_model                  4
% 31.77/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.50  --bmc1_ucm_layered_model                none
% 31.77/4.50  --bmc1_ucm_max_lemma_size               10
% 31.77/4.50  
% 31.77/4.50  ------ AIG Options
% 31.77/4.50  
% 31.77/4.50  --aig_mode                              false
% 31.77/4.50  
% 31.77/4.50  ------ Instantiation Options
% 31.77/4.50  
% 31.77/4.50  --instantiation_flag                    true
% 31.77/4.50  --inst_sos_flag                         true
% 31.77/4.50  --inst_sos_phase                        true
% 31.77/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.50  --inst_lit_sel_side                     num_symb
% 31.77/4.50  --inst_solver_per_active                1400
% 31.77/4.50  --inst_solver_calls_frac                1.
% 31.77/4.50  --inst_passive_queue_type               priority_queues
% 31.77/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.50  --inst_passive_queues_freq              [25;2]
% 31.77/4.50  --inst_dismatching                      true
% 31.77/4.50  --inst_eager_unprocessed_to_passive     true
% 31.77/4.50  --inst_prop_sim_given                   true
% 31.77/4.50  --inst_prop_sim_new                     false
% 31.77/4.50  --inst_subs_new                         false
% 31.77/4.50  --inst_eq_res_simp                      false
% 31.77/4.50  --inst_subs_given                       false
% 31.77/4.50  --inst_orphan_elimination               true
% 31.77/4.50  --inst_learning_loop_flag               true
% 31.77/4.50  --inst_learning_start                   3000
% 31.77/4.50  --inst_learning_factor                  2
% 31.77/4.50  --inst_start_prop_sim_after_learn       3
% 31.77/4.50  --inst_sel_renew                        solver
% 31.77/4.50  --inst_lit_activity_flag                true
% 31.77/4.50  --inst_restr_to_given                   false
% 31.77/4.50  --inst_activity_threshold               500
% 31.77/4.50  --inst_out_proof                        true
% 31.77/4.50  
% 31.77/4.50  ------ Resolution Options
% 31.77/4.50  
% 31.77/4.50  --resolution_flag                       true
% 31.77/4.50  --res_lit_sel                           adaptive
% 31.77/4.50  --res_lit_sel_side                      none
% 31.77/4.50  --res_ordering                          kbo
% 31.77/4.50  --res_to_prop_solver                    active
% 31.77/4.50  --res_prop_simpl_new                    false
% 31.77/4.50  --res_prop_simpl_given                  true
% 31.77/4.50  --res_passive_queue_type                priority_queues
% 31.77/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.50  --res_passive_queues_freq               [15;5]
% 31.77/4.50  --res_forward_subs                      full
% 31.77/4.50  --res_backward_subs                     full
% 31.77/4.50  --res_forward_subs_resolution           true
% 31.77/4.50  --res_backward_subs_resolution          true
% 31.77/4.50  --res_orphan_elimination                true
% 31.77/4.50  --res_time_limit                        2.
% 31.77/4.50  --res_out_proof                         true
% 31.77/4.50  
% 31.77/4.50  ------ Superposition Options
% 31.77/4.50  
% 31.77/4.50  --superposition_flag                    true
% 31.77/4.50  --sup_passive_queue_type                priority_queues
% 31.77/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.50  --demod_completeness_check              fast
% 31.77/4.50  --demod_use_ground                      true
% 31.77/4.50  --sup_to_prop_solver                    passive
% 31.77/4.50  --sup_prop_simpl_new                    true
% 31.77/4.50  --sup_prop_simpl_given                  true
% 31.77/4.50  --sup_fun_splitting                     true
% 31.77/4.50  --sup_smt_interval                      50000
% 31.77/4.50  
% 31.77/4.50  ------ Superposition Simplification Setup
% 31.77/4.50  
% 31.77/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.50  --sup_immed_triv                        [TrivRules]
% 31.77/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_immed_bw_main                     []
% 31.77/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_input_bw                          []
% 31.77/4.50  
% 31.77/4.50  ------ Combination Options
% 31.77/4.50  
% 31.77/4.50  --comb_res_mult                         3
% 31.77/4.50  --comb_sup_mult                         2
% 31.77/4.50  --comb_inst_mult                        10
% 31.77/4.50  
% 31.77/4.50  ------ Debug Options
% 31.77/4.50  
% 31.77/4.50  --dbg_backtrace                         false
% 31.77/4.50  --dbg_dump_prop_clauses                 false
% 31.77/4.50  --dbg_dump_prop_clauses_file            -
% 31.77/4.50  --dbg_out_stat                          false
% 31.77/4.50  ------ Parsing...
% 31.77/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.77/4.50  ------ Proving...
% 31.77/4.50  ------ Problem Properties 
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  clauses                                 34
% 31.77/4.50  conjectures                             8
% 31.77/4.50  EPR                                     2
% 31.77/4.50  Horn                                    26
% 31.77/4.50  unary                                   5
% 31.77/4.50  binary                                  7
% 31.77/4.50  lits                                    105
% 31.77/4.50  lits eq                                 8
% 31.77/4.50  fd_pure                                 0
% 31.77/4.50  fd_pseudo                               0
% 31.77/4.50  fd_cond                                 0
% 31.77/4.50  fd_pseudo_cond                          3
% 31.77/4.50  AC symbols                              0
% 31.77/4.50  
% 31.77/4.50  ------ Schedule dynamic 5 is on 
% 31.77/4.50  
% 31.77/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  ------ 
% 31.77/4.50  Current options:
% 31.77/4.50  ------ 
% 31.77/4.50  
% 31.77/4.50  ------ Input Options
% 31.77/4.50  
% 31.77/4.50  --out_options                           all
% 31.77/4.50  --tptp_safe_out                         true
% 31.77/4.50  --problem_path                          ""
% 31.77/4.50  --include_path                          ""
% 31.77/4.50  --clausifier                            res/vclausify_rel
% 31.77/4.50  --clausifier_options                    ""
% 31.77/4.50  --stdin                                 false
% 31.77/4.50  --stats_out                             all
% 31.77/4.50  
% 31.77/4.50  ------ General Options
% 31.77/4.50  
% 31.77/4.50  --fof                                   false
% 31.77/4.50  --time_out_real                         305.
% 31.77/4.50  --time_out_virtual                      -1.
% 31.77/4.50  --symbol_type_check                     false
% 31.77/4.50  --clausify_out                          false
% 31.77/4.50  --sig_cnt_out                           false
% 31.77/4.50  --trig_cnt_out                          false
% 31.77/4.50  --trig_cnt_out_tolerance                1.
% 31.77/4.50  --trig_cnt_out_sk_spl                   false
% 31.77/4.50  --abstr_cl_out                          false
% 31.77/4.50  
% 31.77/4.50  ------ Global Options
% 31.77/4.50  
% 31.77/4.50  --schedule                              default
% 31.77/4.50  --add_important_lit                     false
% 31.77/4.50  --prop_solver_per_cl                    1000
% 31.77/4.50  --min_unsat_core                        false
% 31.77/4.50  --soft_assumptions                      false
% 31.77/4.50  --soft_lemma_size                       3
% 31.77/4.50  --prop_impl_unit_size                   0
% 31.77/4.50  --prop_impl_unit                        []
% 31.77/4.50  --share_sel_clauses                     true
% 31.77/4.50  --reset_solvers                         false
% 31.77/4.50  --bc_imp_inh                            [conj_cone]
% 31.77/4.50  --conj_cone_tolerance                   3.
% 31.77/4.50  --extra_neg_conj                        none
% 31.77/4.50  --large_theory_mode                     true
% 31.77/4.50  --prolific_symb_bound                   200
% 31.77/4.50  --lt_threshold                          2000
% 31.77/4.50  --clause_weak_htbl                      true
% 31.77/4.50  --gc_record_bc_elim                     false
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing Options
% 31.77/4.50  
% 31.77/4.50  --preprocessing_flag                    true
% 31.77/4.50  --time_out_prep_mult                    0.1
% 31.77/4.50  --splitting_mode                        input
% 31.77/4.50  --splitting_grd                         true
% 31.77/4.50  --splitting_cvd                         false
% 31.77/4.50  --splitting_cvd_svl                     false
% 31.77/4.50  --splitting_nvd                         32
% 31.77/4.50  --sub_typing                            true
% 31.77/4.50  --prep_gs_sim                           true
% 31.77/4.50  --prep_unflatten                        true
% 31.77/4.50  --prep_res_sim                          true
% 31.77/4.50  --prep_upred                            true
% 31.77/4.50  --prep_sem_filter                       exhaustive
% 31.77/4.50  --prep_sem_filter_out                   false
% 31.77/4.50  --pred_elim                             true
% 31.77/4.50  --res_sim_input                         true
% 31.77/4.50  --eq_ax_congr_red                       true
% 31.77/4.50  --pure_diseq_elim                       true
% 31.77/4.50  --brand_transform                       false
% 31.77/4.50  --non_eq_to_eq                          false
% 31.77/4.50  --prep_def_merge                        true
% 31.77/4.50  --prep_def_merge_prop_impl              false
% 31.77/4.50  --prep_def_merge_mbd                    true
% 31.77/4.50  --prep_def_merge_tr_red                 false
% 31.77/4.50  --prep_def_merge_tr_cl                  false
% 31.77/4.50  --smt_preprocessing                     true
% 31.77/4.50  --smt_ac_axioms                         fast
% 31.77/4.50  --preprocessed_out                      false
% 31.77/4.50  --preprocessed_stats                    false
% 31.77/4.50  
% 31.77/4.50  ------ Abstraction refinement Options
% 31.77/4.50  
% 31.77/4.50  --abstr_ref                             []
% 31.77/4.50  --abstr_ref_prep                        false
% 31.77/4.50  --abstr_ref_until_sat                   false
% 31.77/4.50  --abstr_ref_sig_restrict                funpre
% 31.77/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.50  --abstr_ref_under                       []
% 31.77/4.50  
% 31.77/4.50  ------ SAT Options
% 31.77/4.50  
% 31.77/4.50  --sat_mode                              false
% 31.77/4.50  --sat_fm_restart_options                ""
% 31.77/4.50  --sat_gr_def                            false
% 31.77/4.50  --sat_epr_types                         true
% 31.77/4.50  --sat_non_cyclic_types                  false
% 31.77/4.50  --sat_finite_models                     false
% 31.77/4.50  --sat_fm_lemmas                         false
% 31.77/4.50  --sat_fm_prep                           false
% 31.77/4.50  --sat_fm_uc_incr                        true
% 31.77/4.50  --sat_out_model                         small
% 31.77/4.50  --sat_out_clauses                       false
% 31.77/4.50  
% 31.77/4.50  ------ QBF Options
% 31.77/4.50  
% 31.77/4.50  --qbf_mode                              false
% 31.77/4.50  --qbf_elim_univ                         false
% 31.77/4.50  --qbf_dom_inst                          none
% 31.77/4.50  --qbf_dom_pre_inst                      false
% 31.77/4.50  --qbf_sk_in                             false
% 31.77/4.50  --qbf_pred_elim                         true
% 31.77/4.50  --qbf_split                             512
% 31.77/4.50  
% 31.77/4.50  ------ BMC1 Options
% 31.77/4.50  
% 31.77/4.50  --bmc1_incremental                      false
% 31.77/4.50  --bmc1_axioms                           reachable_all
% 31.77/4.50  --bmc1_min_bound                        0
% 31.77/4.50  --bmc1_max_bound                        -1
% 31.77/4.50  --bmc1_max_bound_default                -1
% 31.77/4.50  --bmc1_symbol_reachability              true
% 31.77/4.50  --bmc1_property_lemmas                  false
% 31.77/4.50  --bmc1_k_induction                      false
% 31.77/4.50  --bmc1_non_equiv_states                 false
% 31.77/4.50  --bmc1_deadlock                         false
% 31.77/4.50  --bmc1_ucm                              false
% 31.77/4.50  --bmc1_add_unsat_core                   none
% 31.77/4.50  --bmc1_unsat_core_children              false
% 31.77/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.50  --bmc1_out_stat                         full
% 31.77/4.50  --bmc1_ground_init                      false
% 31.77/4.50  --bmc1_pre_inst_next_state              false
% 31.77/4.50  --bmc1_pre_inst_state                   false
% 31.77/4.50  --bmc1_pre_inst_reach_state             false
% 31.77/4.50  --bmc1_out_unsat_core                   false
% 31.77/4.50  --bmc1_aig_witness_out                  false
% 31.77/4.50  --bmc1_verbose                          false
% 31.77/4.50  --bmc1_dump_clauses_tptp                false
% 31.77/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.50  --bmc1_dump_file                        -
% 31.77/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.50  --bmc1_ucm_extend_mode                  1
% 31.77/4.50  --bmc1_ucm_init_mode                    2
% 31.77/4.50  --bmc1_ucm_cone_mode                    none
% 31.77/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.50  --bmc1_ucm_relax_model                  4
% 31.77/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.50  --bmc1_ucm_layered_model                none
% 31.77/4.50  --bmc1_ucm_max_lemma_size               10
% 31.77/4.50  
% 31.77/4.50  ------ AIG Options
% 31.77/4.50  
% 31.77/4.50  --aig_mode                              false
% 31.77/4.50  
% 31.77/4.50  ------ Instantiation Options
% 31.77/4.50  
% 31.77/4.50  --instantiation_flag                    true
% 31.77/4.50  --inst_sos_flag                         true
% 31.77/4.50  --inst_sos_phase                        true
% 31.77/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.50  --inst_lit_sel_side                     none
% 31.77/4.50  --inst_solver_per_active                1400
% 31.77/4.50  --inst_solver_calls_frac                1.
% 31.77/4.50  --inst_passive_queue_type               priority_queues
% 31.77/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.50  --inst_passive_queues_freq              [25;2]
% 31.77/4.50  --inst_dismatching                      true
% 31.77/4.50  --inst_eager_unprocessed_to_passive     true
% 31.77/4.50  --inst_prop_sim_given                   true
% 31.77/4.50  --inst_prop_sim_new                     false
% 31.77/4.50  --inst_subs_new                         false
% 31.77/4.50  --inst_eq_res_simp                      false
% 31.77/4.50  --inst_subs_given                       false
% 31.77/4.50  --inst_orphan_elimination               true
% 31.77/4.50  --inst_learning_loop_flag               true
% 31.77/4.50  --inst_learning_start                   3000
% 31.77/4.50  --inst_learning_factor                  2
% 31.77/4.50  --inst_start_prop_sim_after_learn       3
% 31.77/4.50  --inst_sel_renew                        solver
% 31.77/4.50  --inst_lit_activity_flag                true
% 31.77/4.50  --inst_restr_to_given                   false
% 31.77/4.50  --inst_activity_threshold               500
% 31.77/4.50  --inst_out_proof                        true
% 31.77/4.50  
% 31.77/4.50  ------ Resolution Options
% 31.77/4.50  
% 31.77/4.50  --resolution_flag                       false
% 31.77/4.50  --res_lit_sel                           adaptive
% 31.77/4.50  --res_lit_sel_side                      none
% 31.77/4.50  --res_ordering                          kbo
% 31.77/4.50  --res_to_prop_solver                    active
% 31.77/4.50  --res_prop_simpl_new                    false
% 31.77/4.50  --res_prop_simpl_given                  true
% 31.77/4.50  --res_passive_queue_type                priority_queues
% 31.77/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.50  --res_passive_queues_freq               [15;5]
% 31.77/4.50  --res_forward_subs                      full
% 31.77/4.50  --res_backward_subs                     full
% 31.77/4.50  --res_forward_subs_resolution           true
% 31.77/4.50  --res_backward_subs_resolution          true
% 31.77/4.50  --res_orphan_elimination                true
% 31.77/4.50  --res_time_limit                        2.
% 31.77/4.50  --res_out_proof                         true
% 31.77/4.50  
% 31.77/4.50  ------ Superposition Options
% 31.77/4.50  
% 31.77/4.50  --superposition_flag                    true
% 31.77/4.50  --sup_passive_queue_type                priority_queues
% 31.77/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.50  --demod_completeness_check              fast
% 31.77/4.50  --demod_use_ground                      true
% 31.77/4.50  --sup_to_prop_solver                    passive
% 31.77/4.50  --sup_prop_simpl_new                    true
% 31.77/4.50  --sup_prop_simpl_given                  true
% 31.77/4.50  --sup_fun_splitting                     true
% 31.77/4.50  --sup_smt_interval                      50000
% 31.77/4.50  
% 31.77/4.50  ------ Superposition Simplification Setup
% 31.77/4.50  
% 31.77/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.50  --sup_immed_triv                        [TrivRules]
% 31.77/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_immed_bw_main                     []
% 31.77/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.50  --sup_input_bw                          []
% 31.77/4.50  
% 31.77/4.50  ------ Combination Options
% 31.77/4.50  
% 31.77/4.50  --comb_res_mult                         3
% 31.77/4.50  --comb_sup_mult                         2
% 31.77/4.50  --comb_inst_mult                        10
% 31.77/4.50  
% 31.77/4.50  ------ Debug Options
% 31.77/4.50  
% 31.77/4.50  --dbg_backtrace                         false
% 31.77/4.50  --dbg_dump_prop_clauses                 false
% 31.77/4.50  --dbg_dump_prop_clauses_file            -
% 31.77/4.50  --dbg_out_stat                          false
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  ------ Proving...
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  % SZS status Theorem for theBenchmark.p
% 31.77/4.50  
% 31.77/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.77/4.50  
% 31.77/4.50  fof(f12,conjecture,(
% 31.77/4.50    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f13,negated_conjecture,(
% 31.77/4.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 31.77/4.50    inference(negated_conjecture,[],[f12])).
% 31.77/4.50  
% 31.77/4.50  fof(f14,plain,(
% 31.77/4.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 31.77/4.50    inference(rectify,[],[f13])).
% 31.77/4.50  
% 31.77/4.50  fof(f15,plain,(
% 31.77/4.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 31.77/4.50    inference(pure_predicate_removal,[],[f14])).
% 31.77/4.50  
% 31.77/4.50  fof(f16,plain,(
% 31.77/4.50    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 31.77/4.50    inference(pure_predicate_removal,[],[f15])).
% 31.77/4.50  
% 31.77/4.50  fof(f26,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 31.77/4.50    inference(ennf_transformation,[],[f16])).
% 31.77/4.50  
% 31.77/4.50  fof(f27,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f26])).
% 31.77/4.50  
% 31.77/4.50  fof(f39,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 31.77/4.50    inference(nnf_transformation,[],[f27])).
% 31.77/4.50  
% 31.77/4.50  fof(f40,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f39])).
% 31.77/4.50  
% 31.77/4.50  fof(f41,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 31.77/4.50    inference(rectify,[],[f40])).
% 31.77/4.50  
% 31.77/4.50  fof(f46,plain,(
% 31.77/4.50    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f45,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f44,plain,(
% 31.77/4.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f43,plain,(
% 31.77/4.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f42,plain,(
% 31.77/4.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f47,plain,(
% 31.77/4.50    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 31.77/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).
% 31.77/4.50  
% 31.77/4.50  fof(f84,plain,(
% 31.77/4.50    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f83,plain,(
% 31.77/4.50    m1_subset_1(sK5,u1_struct_0(sK2))),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f11,axiom,(
% 31.77/4.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f25,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(ennf_transformation,[],[f11])).
% 31.77/4.50  
% 31.77/4.50  fof(f72,plain,(
% 31.77/4.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f25])).
% 31.77/4.50  
% 31.77/4.50  fof(f74,plain,(
% 31.77/4.50    l1_orders_2(sK2)),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f3,axiom,(
% 31.77/4.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f28,plain,(
% 31.77/4.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 31.77/4.50    inference(nnf_transformation,[],[f3])).
% 31.77/4.50  
% 31.77/4.50  fof(f51,plain,(
% 31.77/4.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f28])).
% 31.77/4.50  
% 31.77/4.50  fof(f6,axiom,(
% 31.77/4.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f17,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(ennf_transformation,[],[f6])).
% 31.77/4.50  
% 31.77/4.50  fof(f18,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f17])).
% 31.77/4.50  
% 31.77/4.50  fof(f30,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(nnf_transformation,[],[f18])).
% 31.77/4.50  
% 31.77/4.50  fof(f31,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(rectify,[],[f30])).
% 31.77/4.50  
% 31.77/4.50  fof(f32,plain,(
% 31.77/4.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f33,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 31.77/4.50  
% 31.77/4.50  fof(f55,plain,(
% 31.77/4.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f33])).
% 31.77/4.50  
% 31.77/4.50  fof(f10,axiom,(
% 31.77/4.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f24,plain,(
% 31.77/4.50    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(ennf_transformation,[],[f10])).
% 31.77/4.50  
% 31.77/4.50  fof(f70,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f24])).
% 31.77/4.50  
% 31.77/4.50  fof(f85,plain,(
% 31.77/4.50    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f8,axiom,(
% 31.77/4.50    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f21,plain,(
% 31.77/4.50    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(ennf_transformation,[],[f8])).
% 31.77/4.50  
% 31.77/4.50  fof(f64,plain,(
% 31.77/4.50    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f21])).
% 31.77/4.50  
% 31.77/4.50  fof(f7,axiom,(
% 31.77/4.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f19,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(ennf_transformation,[],[f7])).
% 31.77/4.50  
% 31.77/4.50  fof(f20,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f19])).
% 31.77/4.50  
% 31.77/4.50  fof(f34,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(nnf_transformation,[],[f20])).
% 31.77/4.50  
% 31.77/4.50  fof(f35,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f34])).
% 31.77/4.50  
% 31.77/4.50  fof(f36,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(rectify,[],[f35])).
% 31.77/4.50  
% 31.77/4.50  fof(f37,plain,(
% 31.77/4.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 31.77/4.50    introduced(choice_axiom,[])).
% 31.77/4.50  
% 31.77/4.50  fof(f38,plain,(
% 31.77/4.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 31.77/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 31.77/4.50  
% 31.77/4.50  fof(f59,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f38])).
% 31.77/4.50  
% 31.77/4.50  fof(f87,plain,(
% 31.77/4.50    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(equality_resolution,[],[f59])).
% 31.77/4.50  
% 31.77/4.50  fof(f69,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f24])).
% 31.77/4.50  
% 31.77/4.50  fof(f9,axiom,(
% 31.77/4.50    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f22,plain,(
% 31.77/4.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 31.77/4.50    inference(ennf_transformation,[],[f9])).
% 31.77/4.50  
% 31.77/4.50  fof(f23,plain,(
% 31.77/4.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 31.77/4.50    inference(flattening,[],[f22])).
% 31.77/4.50  
% 31.77/4.50  fof(f66,plain,(
% 31.77/4.50    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f23])).
% 31.77/4.50  
% 31.77/4.50  fof(f73,plain,(
% 31.77/4.50    v4_orders_2(sK2)),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f58,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f33])).
% 31.77/4.50  
% 31.77/4.50  fof(f56,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f33])).
% 31.77/4.50  
% 31.77/4.50  fof(f57,plain,(
% 31.77/4.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f33])).
% 31.77/4.50  
% 31.77/4.50  fof(f4,axiom,(
% 31.77/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f29,plain,(
% 31.77/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.77/4.50    inference(nnf_transformation,[],[f4])).
% 31.77/4.50  
% 31.77/4.50  fof(f53,plain,(
% 31.77/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f29])).
% 31.77/4.50  
% 31.77/4.50  fof(f5,axiom,(
% 31.77/4.50    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f54,plain,(
% 31.77/4.50    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f5])).
% 31.77/4.50  
% 31.77/4.50  fof(f77,plain,(
% 31.77/4.50    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f82,plain,(
% 31.77/4.50    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f1,axiom,(
% 31.77/4.50    v1_xboole_0(k1_xboole_0)),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f48,plain,(
% 31.77/4.50    v1_xboole_0(k1_xboole_0)),
% 31.77/4.50    inference(cnf_transformation,[],[f1])).
% 31.77/4.50  
% 31.77/4.50  fof(f2,axiom,(
% 31.77/4.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 31.77/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.50  
% 31.77/4.50  fof(f49,plain,(
% 31.77/4.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f2])).
% 31.77/4.50  
% 31.77/4.50  fof(f81,plain,(
% 31.77/4.50    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f60,plain,(
% 31.77/4.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(cnf_transformation,[],[f38])).
% 31.77/4.50  
% 31.77/4.50  fof(f86,plain,(
% 31.77/4.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 31.77/4.50    inference(equality_resolution,[],[f60])).
% 31.77/4.50  
% 31.77/4.50  fof(f80,plain,(
% 31.77/4.50    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f79,plain,(
% 31.77/4.50    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f47])).
% 31.77/4.50  
% 31.77/4.50  fof(f52,plain,(
% 31.77/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.77/4.50    inference(cnf_transformation,[],[f29])).
% 31.77/4.50  
% 31.77/4.50  cnf(c_26,negated_conjecture,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 31.77/4.50      inference(cnf_transformation,[],[f84]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4137,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_27,negated_conjecture,
% 31.77/4.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(cnf_transformation,[],[f83]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4136,plain,
% 31.77/4.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_23,plain,
% 31.77/4.50      ( ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ r1_tarski(X3,X1)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_36,negated_conjecture,
% 31.77/4.50      ( l1_orders_2(sK2) ),
% 31.77/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_833,plain,
% 31.77/4.50      ( ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ r1_tarski(X3,X1)
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_23,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_834,plain,
% 31.77/4.50      ( ~ r2_lattice3(sK2,X0,X1)
% 31.77/4.50      | r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ r1_tarski(X2,X0) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_833]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4122,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X2,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(X2,X0) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5068,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 31.77/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_4122]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5073,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 31.77/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4137,c_5068]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_2,plain,
% 31.77/4.50      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 31.77/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4142,plain,
% 31.77/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_10,plain,
% 31.77/4.50      ( r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ r2_hidden(X1,X3)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_993,plain,
% 31.77/4.50      ( r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ r2_hidden(X1,X3)
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_10,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_994,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(X0,X2) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_993]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4113,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(X0,X2) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5394,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,X0) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,X0) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK5,X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_4113]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5455,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r2_hidden(sK5,X0) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_5394]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5464,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r2_hidden(sK5,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_5073,c_5455]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_19,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,X1,X2)
% 31.77/4.50      | r2_lattice3(X0,k1_tarski(X1),X2)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f70]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_903,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,X1,X2)
% 31.77/4.50      | r2_lattice3(X0,k1_tarski(X1),X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_904,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,X0,X1)
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X0),X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_903]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4118,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5108,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4118,c_5068]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_60,plain,
% 31.77/4.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5995,plain,
% 31.77/4.50      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 31.77/4.50      | r1_orders_2(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_5108,c_60]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5996,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_5995]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_6001,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_5996]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9381,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 31.77/4.50      | r2_hidden(sK5,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(X1,k1_tarski(sK5)) != iProver_top
% 31.77/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_5464,c_6001]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_30529,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X1),sK5) = iProver_top
% 31.77/4.50      | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
% 31.77/4.50      | r2_hidden(sK5,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4142,c_9381]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_25,negated_conjecture,
% 31.77/4.50      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 31.77/4.50      inference(cnf_transformation,[],[f85]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4138,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_32054,plain,
% 31.77/4.50      ( r2_lattice3(sK2,k1_tarski(X0),sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top
% 31.77/4.50      | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
% 31.77/4.50      | r2_hidden(sK5,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(sK3,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_30529,c_4138]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_16,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_921,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_922,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_921]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4117,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_15,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f87]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_227,plain,
% 31.77/4.50      ( ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_15,c_16]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_228,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_227]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_805,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_228,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_806,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) | ~ r1_yellow_0(sK2,X0) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_805]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4124,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) = iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X0) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5069,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X2,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r1_tarski(X2,X0) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4117,c_4122]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5962,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4124,c_5069]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_20,plain,
% 31.77/4.50      ( r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_885,plain,
% 31.77/4.50      ( r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_886,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_885]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4119,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5988,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_5962,c_4119]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_10334,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4117,c_5988]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_17,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X3,X1)
% 31.77/4.50      | r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ v4_orders_2(X0)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_37,negated_conjecture,
% 31.77/4.50      ( v4_orders_2(sK2) ),
% 31.77/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_546,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,X1,X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X3,X1)
% 31.77/4.50      | r2_lattice3(X0,X3,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0)
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_547,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,X0,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X2,X0)
% 31.77/4.50      | r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ l1_orders_2(sK2) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_546]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_549,plain,
% 31.77/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X2,X0)
% 31.77/4.50      | ~ r1_orders_2(sK2,X0,X1) ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_547,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_550,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,X0,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X2,X0)
% 31.77/4.50      | r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_549]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4129,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X2,X0) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X2,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5492,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,X0) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,X0) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_4129]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5502,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK5,k1_yellow_0(sK2,X0)) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,k1_yellow_0(sK2,X0)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4117,c_5492]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_10388,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_10334,c_5502]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_71134,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_10388,c_60]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_71135,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_71134]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_71144,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_71135,c_4119]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_71999,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(X0),sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4117,c_71144]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_7,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 31.77/4.50      | r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1044,plain,
% 31.77/4.50      ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 31.77/4.50      | r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_7,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1045,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 31.77/4.50      | r2_lattice3(sK2,X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_1044]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4110,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_72017,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_71999,c_4110]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1014,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_9,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1015,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_1014]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4248,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1))
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_1015]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4249,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,k1_yellow_0(sK2,X1)),u1_struct_0(sK2)) = iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4248]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_72479,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_72017,c_4249]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_72480,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,X0,k1_yellow_0(sK2,X1))),sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_72479]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_72500,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X1)) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X1) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,X0,k1_yellow_0(sK2,X1)),k1_tarski(sK5)) != iProver_top
% 31.77/4.50      | r2_hidden(sK5,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK5),X1) != iProver_top
% 31.77/4.50      | r1_tarski(sK3,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_32054,c_72480]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_62,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4243,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5)
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_1015]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4757,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5)
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4243]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4758,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4757]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4316,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
% 31.77/4.50      | r2_lattice3(sK2,X0,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_1045]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4756,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 31.77/4.50      | r2_lattice3(sK2,sK3,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4316]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4760,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4756]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_8,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1029,plain,
% 31.77/4.50      ( r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_8,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1030,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_1029]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4303,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | r2_hidden(sK0(sK2,X0,sK5),X0) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_1030]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4755,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4303]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4762,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4755]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4501,plain,
% 31.77/4.50      ( ~ r2_hidden(X0,sK3) | r1_tarski(k1_tarski(X0),sK3) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5088,plain,
% 31.77/4.50      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 31.77/4.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4501]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5089,plain,
% 31.77/4.50      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_5088]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4281,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,k1_tarski(X0),sK5)
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_886]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5604,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 31.77/4.50      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4281]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5613,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) != iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_5604]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4,plain,
% 31.77/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.77/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4224,plain,
% 31.77/4.50      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 31.77/4.50      | ~ r1_tarski(k1_tarski(X0),sK3) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5806,plain,
% 31.77/4.50      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 31.77/4.50      | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4224]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5807,plain,
% 31.77/4.50      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 31.77/4.50      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_5806]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_6,plain,
% 31.77/4.50      ( v1_finset_1(k1_tarski(X0)) ),
% 31.77/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_33,negated_conjecture,
% 31.77/4.50      ( r1_yellow_0(sK2,X0)
% 31.77/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 31.77/4.50      | ~ v1_finset_1(X0)
% 31.77/4.50      | k1_xboole_0 = X0 ),
% 31.77/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_581,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,X0)
% 31.77/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 31.77/4.50      | k1_tarski(X1) != X0
% 31.77/4.50      | k1_xboole_0 = X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_6,c_33]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_582,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,k1_tarski(X0))
% 31.77/4.50      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 31.77/4.50      | k1_xboole_0 = k1_tarski(X0) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_581]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9033,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 31.77/4.50      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 31.77/4.50      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_582]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9034,plain,
% 31.77/4.50      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 31.77/4.50      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 31.77/4.50      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_9033]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_28,negated_conjecture,
% 31.77/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 31.77/4.50      | ~ v1_finset_1(X0)
% 31.77/4.50      | k1_xboole_0 = X0 ),
% 31.77/4.50      inference(cnf_transformation,[],[f82]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_596,plain,
% 31.77/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 31.77/4.50      | k1_tarski(X1) != X0
% 31.77/4.50      | k1_xboole_0 = X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_597,plain,
% 31.77/4.50      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 31.77/4.50      | k1_xboole_0 = k1_tarski(X0) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_596]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9032,plain,
% 31.77/4.50      ( ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 31.77/4.50      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_597]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_9036,plain,
% 31.77/4.50      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 31.77/4.50      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_9032]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4363,plain,
% 31.77/4.50      ( r1_orders_2(sK2,X0,sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,X1,sK5)
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(X0,X1) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_994]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4478,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,X1,sK5)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(k1_yellow_0(sK2,X0),X1) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4363]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_25066,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,sK4,sK5)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4478]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_25067,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) != iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_25066]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_25098,plain,
% 31.77/4.50      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 31.77/4.50      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_806]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_25099,plain,
% 31.77/4.50      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) = iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_25098]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_44580,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_922]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_44581,plain,
% 31.77/4.50      ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_44580]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4357,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 31.77/4.50      | r2_lattice3(sK2,X2,X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X2,k1_yellow_0(sK2,X0))
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_550]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4607,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,X1,k1_yellow_0(sK2,X0))
% 31.77/4.50      | r2_lattice3(sK2,X1,sK5)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4357]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_6422,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,X0),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,X0))
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4607]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_44990,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5)
% 31.77/4.50      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_6422]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_44997,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_44990]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_3312,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_13997,plain,
% 31.77/4.50      ( X0 != X1 | k1_tarski(X2) != X1 | k1_tarski(X2) = X0 ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_3312]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_41590,plain,
% 31.77/4.50      ( X0 != k1_tarski(X1)
% 31.77/4.50      | k1_tarski(X1) = X0
% 31.77/4.50      | k1_tarski(X1) != k1_tarski(X1) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_13997]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_51427,plain,
% 31.77/4.50      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 31.77/4.50      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 31.77/4.50      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_41590]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_3311,plain,( X0 = X0 ),theory(equality) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_63256,plain,
% 31.77/4.50      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_3311]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_0,plain,
% 31.77/4.50      ( v1_xboole_0(k1_xboole_0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_1,plain,
% 31.77/4.50      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 31.77/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_517,plain,
% 31.77/4.50      ( k1_tarski(X0) != k1_xboole_0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_70402,plain,
% 31.77/4.50      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_517]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73068,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_72500,c_60,c_62,c_4758,c_4760,c_4762,c_5089,c_5613,
% 31.77/4.50                 c_5807,c_9034,c_9036,c_25067,c_25099,c_44581,c_44997,
% 31.77/4.50                 c_51427,c_63256,c_70402]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73074,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 31.77/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_5073,c_73068]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4111,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4112,plain,
% 31.77/4.50      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_29,negated_conjecture,
% 31.77/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(X0,sK4)
% 31.77/4.50      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 31.77/4.50      inference(cnf_transformation,[],[f81]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4135,plain,
% 31.77/4.50      ( k1_yellow_0(sK2,sK6(X0)) = X0
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(X0,sK4) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5735,plain,
% 31.77/4.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,X0,X1))) = sK0(sK2,X0,X1)
% 31.77/4.50      | r2_lattice3(sK2,X0,X1) = iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,X0,X1),sK4) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4112,c_4135]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5851,plain,
% 31.77/4.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 31.77/4.50      | r2_lattice3(sK2,sK4,X0) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4111,c_5735]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_11110,plain,
% 31.77/4.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4136,c_5851]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73072,plain,
% 31.77/4.50      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_11110,c_73068]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_14,plain,
% 31.77/4.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_234,plain,
% 31.77/4.50      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_14,c_16]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_235,plain,
% 31.77/4.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | ~ l1_orders_2(X0) ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_234]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_787,plain,
% 31.77/4.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 31.77/4.50      | ~ r2_lattice3(X0,X1,X2)
% 31.77/4.50      | ~ r1_yellow_0(X0,X1)
% 31.77/4.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.77/4.50      | sK2 != X0 ),
% 31.77/4.50      inference(resolution_lifted,[status(thm)],[c_235,c_36]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_788,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 31.77/4.50      | ~ r2_lattice3(sK2,X0,X1)
% 31.77/4.50      | ~ r1_yellow_0(sK2,X0)
% 31.77/4.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(unflattening,[status(thm)],[c_787]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4125,plain,
% 31.77/4.50      ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,X0,X1) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,X0) != iProver_top
% 31.77/4.50      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73204,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
% 31.77/4.50      | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_73072,c_4125]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4420,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK4,sK5)
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4243]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4421,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4420]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4460,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK4,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 31.77/4.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4303]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4461,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4460]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_30,negated_conjecture,
% 31.77/4.50      ( r1_yellow_0(sK2,sK6(X0))
% 31.77/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(X0,sK4) ),
% 31.77/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5146,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 31.77/4.50      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 31.77/4.50      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_30]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5147,plain,
% 31.77/4.50      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
% 31.77/4.50      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_5146]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_74866,plain,
% 31.77/4.50      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
% 31.77/4.50      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(global_propositional_subsumption,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_73204,c_60,c_62,c_4421,c_4461,c_4758,c_4760,c_4762,
% 31.77/4.50                 c_5089,c_5147,c_5613,c_5807,c_9034,c_9036,c_25067,
% 31.77/4.50                 c_25099,c_44581,c_44997,c_51427,c_63256,c_70402]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_74867,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),X0) = iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0) != iProver_top
% 31.77/4.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(renaming,[status(thm)],[c_74866]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_74878,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_73074,c_74867]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_31,negated_conjecture,
% 31.77/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 31.77/4.50      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
% 31.77/4.50      | ~ r2_hidden(X0,sK4) ),
% 31.77/4.50      inference(cnf_transformation,[],[f79]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4133,plain,
% 31.77/4.50      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) = iProver_top
% 31.77/4.50      | r2_hidden(X0,sK4) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5,plain,
% 31.77/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.77/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4139,plain,
% 31.77/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.77/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4548,plain,
% 31.77/4.50      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 31.77/4.50      | r2_hidden(X0,sK4) != iProver_top
% 31.77/4.50      | r1_tarski(sK6(X0),sK3) = iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4133,c_4139]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_5020,plain,
% 31.77/4.50      ( r2_hidden(k1_yellow_0(sK2,X0),sK4) != iProver_top
% 31.77/4.50      | r1_tarski(sK6(k1_yellow_0(sK2,X0)),sK3) = iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_4117,c_4548]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73205,plain,
% 31.77/4.50      ( r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) != iProver_top
% 31.77/4.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
% 31.77/4.50      inference(superposition,[status(thm)],[c_73072,c_5020]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_73436,plain,
% 31.77/4.50      ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 31.77/4.50      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
% 31.77/4.50      inference(demodulation,[status(thm)],[c_73205,c_73072]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4423,plain,
% 31.77/4.50      ( ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5)
% 31.77/4.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 31.77/4.50      inference(instantiation,[status(thm)],[c_4316]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(c_4424,plain,
% 31.77/4.50      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
% 31.77/4.50      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 31.77/4.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 31.77/4.50      inference(predicate_to_equality,[status(thm)],[c_4423]) ).
% 31.77/4.50  
% 31.77/4.50  cnf(contradiction,plain,
% 31.77/4.50      ( $false ),
% 31.77/4.50      inference(minisat,
% 31.77/4.50                [status(thm)],
% 31.77/4.50                [c_74878,c_73436,c_73068,c_4461,c_4424,c_60]) ).
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.77/4.50  
% 31.77/4.50  ------                               Statistics
% 31.77/4.50  
% 31.77/4.50  ------ General
% 31.77/4.50  
% 31.77/4.50  abstr_ref_over_cycles:                  0
% 31.77/4.50  abstr_ref_under_cycles:                 0
% 31.77/4.50  gc_basic_clause_elim:                   0
% 31.77/4.50  forced_gc_time:                         0
% 31.77/4.50  parsing_time:                           0.015
% 31.77/4.50  unif_index_cands_time:                  0.
% 31.77/4.50  unif_index_add_time:                    0.
% 31.77/4.50  orderings_time:                         0.
% 31.77/4.50  out_proof_time:                         0.026
% 31.77/4.50  total_time:                             3.659
% 31.77/4.50  num_of_symbols:                         54
% 31.77/4.50  num_of_terms:                           41608
% 31.77/4.50  
% 31.77/4.50  ------ Preprocessing
% 31.77/4.50  
% 31.77/4.50  num_of_splits:                          0
% 31.77/4.50  num_of_split_atoms:                     0
% 31.77/4.50  num_of_reused_defs:                     0
% 31.77/4.50  num_eq_ax_congr_red:                    28
% 31.77/4.50  num_of_sem_filtered_clauses:            1
% 31.77/4.50  num_of_subtypes:                        0
% 31.77/4.50  monotx_restored_types:                  0
% 31.77/4.50  sat_num_of_epr_types:                   0
% 31.77/4.50  sat_num_of_non_cyclic_types:            0
% 31.77/4.50  sat_guarded_non_collapsed_types:        0
% 31.77/4.50  num_pure_diseq_elim:                    0
% 31.77/4.50  simp_replaced_by:                       0
% 31.77/4.50  res_preprocessed:                       169
% 31.77/4.50  prep_upred:                             0
% 31.77/4.50  prep_unflattend:                        152
% 31.77/4.50  smt_new_axioms:                         0
% 31.77/4.50  pred_elim_cands:                        7
% 31.77/4.50  pred_elim:                              4
% 31.77/4.50  pred_elim_cl:                           4
% 31.77/4.50  pred_elim_cycles:                       11
% 31.77/4.50  merged_defs:                            24
% 31.77/4.50  merged_defs_ncl:                        0
% 31.77/4.50  bin_hyper_res:                          24
% 31.77/4.50  prep_cycles:                            4
% 31.77/4.50  pred_elim_time:                         0.045
% 31.77/4.50  splitting_time:                         0.
% 31.77/4.50  sem_filter_time:                        0.
% 31.77/4.50  monotx_time:                            0.001
% 31.77/4.50  subtype_inf_time:                       0.
% 31.77/4.50  
% 31.77/4.50  ------ Problem properties
% 31.77/4.50  
% 31.77/4.50  clauses:                                34
% 31.77/4.50  conjectures:                            8
% 31.77/4.50  epr:                                    2
% 31.77/4.50  horn:                                   26
% 31.77/4.50  ground:                                 5
% 31.77/4.50  unary:                                  5
% 31.77/4.50  binary:                                 7
% 31.77/4.50  lits:                                   105
% 31.77/4.50  lits_eq:                                8
% 31.77/4.50  fd_pure:                                0
% 31.77/4.50  fd_pseudo:                              0
% 31.77/4.50  fd_cond:                                0
% 31.77/4.50  fd_pseudo_cond:                         3
% 31.77/4.50  ac_symbols:                             0
% 31.77/4.50  
% 31.77/4.50  ------ Propositional Solver
% 31.77/4.50  
% 31.77/4.50  prop_solver_calls:                      45
% 31.77/4.50  prop_fast_solver_calls:                 7703
% 31.77/4.50  smt_solver_calls:                       0
% 31.77/4.50  smt_fast_solver_calls:                  0
% 31.77/4.50  prop_num_of_clauses:                    34707
% 31.77/4.50  prop_preprocess_simplified:             54319
% 31.77/4.50  prop_fo_subsumed:                       276
% 31.77/4.50  prop_solver_time:                       0.
% 31.77/4.50  smt_solver_time:                        0.
% 31.77/4.50  smt_fast_solver_time:                   0.
% 31.77/4.50  prop_fast_solver_time:                  0.
% 31.77/4.50  prop_unsat_core_time:                   0.002
% 31.77/4.50  
% 31.77/4.50  ------ QBF
% 31.77/4.50  
% 31.77/4.50  qbf_q_res:                              0
% 31.77/4.50  qbf_num_tautologies:                    0
% 31.77/4.50  qbf_prep_cycles:                        0
% 31.77/4.50  
% 31.77/4.50  ------ BMC1
% 31.77/4.50  
% 31.77/4.50  bmc1_current_bound:                     -1
% 31.77/4.50  bmc1_last_solved_bound:                 -1
% 31.77/4.50  bmc1_unsat_core_size:                   -1
% 31.77/4.50  bmc1_unsat_core_parents_size:           -1
% 31.77/4.50  bmc1_merge_next_fun:                    0
% 31.77/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.77/4.50  
% 31.77/4.50  ------ Instantiation
% 31.77/4.50  
% 31.77/4.50  inst_num_of_clauses:                    1315
% 31.77/4.50  inst_num_in_passive:                    93
% 31.77/4.50  inst_num_in_active:                     2767
% 31.77/4.50  inst_num_in_unprocessed:                318
% 31.77/4.50  inst_num_of_loops:                      3939
% 31.77/4.50  inst_num_of_learning_restarts:          1
% 31.77/4.50  inst_num_moves_active_passive:          1163
% 31.77/4.50  inst_lit_activity:                      0
% 31.77/4.50  inst_lit_activity_moves:                3
% 31.77/4.50  inst_num_tautologies:                   0
% 31.77/4.50  inst_num_prop_implied:                  0
% 31.77/4.50  inst_num_existing_simplified:           0
% 31.77/4.50  inst_num_eq_res_simplified:             0
% 31.77/4.50  inst_num_child_elim:                    0
% 31.77/4.50  inst_num_of_dismatching_blockings:      6142
% 31.77/4.50  inst_num_of_non_proper_insts:           9795
% 31.77/4.50  inst_num_of_duplicates:                 0
% 31.77/4.50  inst_inst_num_from_inst_to_res:         0
% 31.77/4.50  inst_dismatching_checking_time:         0.
% 31.77/4.50  
% 31.77/4.50  ------ Resolution
% 31.77/4.50  
% 31.77/4.50  res_num_of_clauses:                     48
% 31.77/4.50  res_num_in_passive:                     48
% 31.77/4.50  res_num_in_active:                      0
% 31.77/4.50  res_num_of_loops:                       173
% 31.77/4.50  res_forward_subset_subsumed:            208
% 31.77/4.50  res_backward_subset_subsumed:           0
% 31.77/4.50  res_forward_subsumed:                   1
% 31.77/4.50  res_backward_subsumed:                  0
% 31.77/4.50  res_forward_subsumption_resolution:     5
% 31.77/4.50  res_backward_subsumption_resolution:    0
% 31.77/4.50  res_clause_to_clause_subsumption:       61860
% 31.77/4.50  res_orphan_elimination:                 0
% 31.77/4.50  res_tautology_del:                      770
% 31.77/4.50  res_num_eq_res_simplified:              0
% 31.77/4.50  res_num_sel_changes:                    0
% 31.77/4.50  res_moves_from_active_to_pass:          0
% 31.77/4.50  
% 31.77/4.50  ------ Superposition
% 31.77/4.50  
% 31.77/4.50  sup_time_total:                         0.
% 31.77/4.50  sup_time_generating:                    0.
% 31.77/4.50  sup_time_sim_full:                      0.
% 31.77/4.50  sup_time_sim_immed:                     0.
% 31.77/4.50  
% 31.77/4.50  sup_num_of_clauses:                     3787
% 31.77/4.50  sup_num_in_active:                      487
% 31.77/4.50  sup_num_in_passive:                     3300
% 31.77/4.50  sup_num_of_loops:                       787
% 31.77/4.50  sup_fw_superposition:                   3247
% 31.77/4.50  sup_bw_superposition:                   2974
% 31.77/4.50  sup_immediate_simplified:               1608
% 31.77/4.50  sup_given_eliminated:                   30
% 31.77/4.50  comparisons_done:                       0
% 31.77/4.50  comparisons_avoided:                    11
% 31.77/4.50  
% 31.77/4.50  ------ Simplifications
% 31.77/4.50  
% 31.77/4.50  
% 31.77/4.50  sim_fw_subset_subsumed:                 289
% 31.77/4.50  sim_bw_subset_subsumed:                 366
% 31.77/4.50  sim_fw_subsumed:                        1101
% 31.77/4.50  sim_bw_subsumed:                        277
% 31.77/4.50  sim_fw_subsumption_res:                 0
% 31.77/4.50  sim_bw_subsumption_res:                 0
% 31.77/4.50  sim_tautology_del:                      65
% 31.77/4.50  sim_eq_tautology_del:                   3
% 31.77/4.50  sim_eq_res_simp:                        6
% 31.77/4.50  sim_fw_demodulated:                     159
% 31.77/4.50  sim_bw_demodulated:                     0
% 31.77/4.50  sim_light_normalised:                   8
% 31.77/4.50  sim_joinable_taut:                      0
% 31.77/4.50  sim_joinable_simp:                      0
% 31.77/4.50  sim_ac_normalised:                      0
% 31.77/4.50  sim_smt_subsumption:                    0
% 31.77/4.50  
%------------------------------------------------------------------------------
