%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:10 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  253 (2272 expanded)
%              Number of clauses        :  177 ( 557 expanded)
%              Number of leaves         :   19 ( 586 expanded)
%              Depth                    :   38
%              Number of atoms          : 1287 (35256 expanded)
%              Number of equality atoms :  360 (4929 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X5] :
      ( k2_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X7] :
      ( r2_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f58])).

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

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    v4_orders_2(sK2) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X5] :
      ( r2_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2944,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3677,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2944])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_899,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_900,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_2918,plain,
    ( r1_lattice3(sK2,X0_52,X1_52)
    | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_900])).

cnf(c_3702,plain,
    ( r1_lattice3(sK2,X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_884,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_885,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_2919,plain,
    ( r1_lattice3(sK2,X0_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_885])).

cnf(c_3701,plain,
    ( r1_lattice3(sK2,X0_52,X1_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2943,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3678,plain,
    ( k2_yellow_0(sK2,sK6(X0_52)) = X0_52
    | r2_hidden(X0_52,sK4) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2943])).

cnf(c_5282,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,X0_52,X1_52))) = sK0(sK2,X0_52,X1_52)
    | r1_lattice3(sK2,X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,X1_52),sK4) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_3678])).

cnf(c_5863,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_52))) = sK0(sK2,sK4,X0_52)
    | r1_lattice3(sK2,sK4,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_5282])).

cnf(c_6364,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_5863])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2947,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3674,plain,
    ( r2_hidden(X0_52,X1_52) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2947])).

cnf(c_4,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_599,plain,
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_600,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_2934,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_52)),sK4)
    | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_52) ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_3686,plain,
    ( k1_xboole_0 = k1_tarski(X0_52)
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_52)),sK4) = iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2934])).

cnf(c_14,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_769,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_770,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_2925,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_770])).

cnf(c_3695,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2925])).

cnf(c_4213,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,X0_52))) = k2_yellow_0(sK2,X0_52)
    | r2_hidden(k2_yellow_0(sK2,X0_52),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_3678])).

cnf(c_5240,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
    | k1_tarski(X0_52) = k1_xboole_0
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3686,c_4213])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_470,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_2938,plain,
    ( k1_tarski(X0_52) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_6293,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5240,c_2938])).

cnf(c_6299,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_6293])).

cnf(c_6359,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52)))
    | r1_lattice3(sK2,sK3,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_6299])).

cnf(c_7993,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r1_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_6359])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_476,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_477,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_669,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_477,c_34])).

cnf(c_670,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_2931,plain,
    ( ~ r1_lattice3(sK2,X0_52,X1_52)
    | r1_lattice3(sK2,X2_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_670])).

cnf(c_3689,plain,
    ( r1_lattice3(sK2,X0_52,X1_52) != iProver_top
    | r1_lattice3(sK2,X2_52,X1_52) = iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2931])).

cnf(c_4626,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_3689])).

cnf(c_8045,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7993,c_4626])).

cnf(c_8692,plain,
    ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_8045])).

cnf(c_3778,plain,
    ( ~ r2_hidden(X0_52,sK3)
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_3779,plain,
    ( r2_hidden(X0_52,sK3) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3778])).

cnf(c_24,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2945,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3676,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2945])).

cnf(c_4668,plain,
    ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_4626])).

cnf(c_4971,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_4668])).

cnf(c_31,negated_conjecture,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_584,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_585,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_2935,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0_52))
    | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_52) ),
    inference(subtyping,[status(esa)],[c_585])).

cnf(c_3685,plain,
    ( k1_xboole_0 = k1_tarski(X0_52)
    | r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_5235,plain,
    ( k1_tarski(X0_52) = k1_xboole_0
    | r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_3685])).

cnf(c_5815,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_2938])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_863,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_864,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_2920,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r1_lattice3(sK2,X2_52,X0_52)
    | ~ r2_hidden(X1_52,X2_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_864])).

cnf(c_3700,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
    | r1_lattice3(sK2,X2_52,X0_52) != iProver_top
    | r2_hidden(X1_52,X2_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2920])).

cnf(c_4806,plain,
    ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
    | r1_lattice3(sK2,X1_52,sK5) != iProver_top
    | r2_hidden(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_3700])).

cnf(c_4864,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) = iProver_top
    | r1_lattice3(sK2,X1_52,sK5) != iProver_top
    | r2_hidden(k2_yellow_0(sK2,X0_52),X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_4806])).

cnf(c_5942,plain,
    ( k1_tarski(X0_52) = k1_xboole_0
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0_52))) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3686,c_4864])).

cnf(c_8425,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0_52))) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5942,c_2938])).

cnf(c_13,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_215,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_216,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_685,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_216,c_34])).

cnf(c_686,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_2930,plain,
    ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52))
    | ~ r2_yellow_0(sK2,X0_52) ),
    inference(subtyping,[status(esa)],[c_686])).

cnf(c_3690,plain,
    ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52)) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2930])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_526,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X2)
    | r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_527,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,X2,X0)
    | ~ r1_lattice3(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_34])).

cnf(c_530,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X1)
    | r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_2937,plain,
    ( ~ r1_orders_2(sK2,X0_52,X1_52)
    | ~ r1_lattice3(sK2,X2_52,X1_52)
    | r1_lattice3(sK2,X2_52,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_3683,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
    | r1_lattice3(sK2,X2_52,X1_52) != iProver_top
    | r1_lattice3(sK2,X2_52,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2937])).

cnf(c_4532,plain,
    ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
    | r1_lattice3(sK2,X1_52,X0_52) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3677,c_3683])).

cnf(c_4621,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) != iProver_top
    | r1_lattice3(sK2,X1_52,k2_yellow_0(sK2,X0_52)) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_4532])).

cnf(c_6143,plain,
    ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) != iProver_top
    | r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_4621])).

cnf(c_8433,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_yellow_0(sK2,k1_tarski(X0_52)) != iProver_top
    | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8425,c_6143])).

cnf(c_8778,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8692,c_3779,c_4971,c_5815,c_8433])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_697,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_698,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_2929,plain,
    ( r1_orders_2(sK2,X0_52,X1_52)
    | ~ r1_lattice3(sK2,k1_tarski(X1_52),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_698])).

cnf(c_3691,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_52),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2929])).

cnf(c_8784,plain,
    ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8778,c_3691])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9024,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8784,c_58])).

cnf(c_9025,plain,
    ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
    | r2_hidden(X0_52,sK3) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9024])).

cnf(c_9031,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,X1_52)) = iProver_top
    | r1_lattice3(sK2,X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,X1_52),sK3) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_9025])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_914,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_34])).

cnf(c_915,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_2917,plain,
    ( ~ r1_orders_2(sK2,X0_52,sK0(sK2,X1_52,X0_52))
    | r1_lattice3(sK2,X1_52,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_915])).

cnf(c_3703,plain,
    ( r1_orders_2(sK2,X0_52,sK0(sK2,X1_52,X0_52)) != iProver_top
    | r1_lattice3(sK2,X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_9738,plain,
    ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9031,c_3703])).

cnf(c_9766,plain,
    ( r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top
    | r1_lattice3(sK2,X0_52,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9738,c_58])).

cnf(c_9767,plain,
    ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9766])).

cnf(c_9772,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_9767])).

cnf(c_9775,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9772,c_58])).

cnf(c_23,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2946,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3675,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2946])).

cnf(c_9779,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9775,c_3675])).

cnf(c_9821,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_6364,c_9779])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_778,plain,
    ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ r2_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_779,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
    | ~ r1_lattice3(sK2,X1,X0)
    | ~ r2_yellow_0(sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_788,plain,
    ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
    | ~ r1_lattice3(sK2,X1,X0)
    | ~ r2_yellow_0(sK2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_779,c_770])).

cnf(c_2924,plain,
    ( r1_orders_2(sK2,X0_52,k2_yellow_0(sK2,X1_52))
    | ~ r1_lattice3(sK2,X1_52,X0_52)
    | ~ r2_yellow_0(sK2,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_788])).

cnf(c_3696,plain,
    ( r1_orders_2(sK2,X0_52,k2_yellow_0(sK2,X1_52)) = iProver_top
    | r1_lattice3(sK2,X1_52,X0_52) != iProver_top
    | r2_yellow_0(sK2,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_715,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_lattice3(X0,k1_tarski(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_716,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_lattice3(sK2,k1_tarski(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_2928,plain,
    ( ~ r1_orders_2(sK2,X0_52,X1_52)
    | r1_lattice3(sK2,k1_tarski(X1_52),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_716])).

cnf(c_3692,plain,
    ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_52),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2928])).

cnf(c_4758,plain,
    ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_4626])).

cnf(c_6621,plain,
    ( m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4758,c_58])).

cnf(c_6622,plain,
    ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
    | r1_lattice3(sK2,X1_52,sK5) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6621])).

cnf(c_6627,plain,
    ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
    | r2_hidden(X1_52,k1_tarski(X0_52)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_6622])).

cnf(c_6632,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | r2_hidden(X1_52,k1_tarski(k2_yellow_0(sK2,X0_52))) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3696,c_6627])).

cnf(c_3015,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2925])).

cnf(c_12369,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | r2_hidden(X1_52,k1_tarski(k2_yellow_0(sK2,X0_52))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6632,c_58,c_3015])).

cnf(c_12373,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_12369])).

cnf(c_12447,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
    | r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12373,c_3691])).

cnf(c_15883,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
    | r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12447,c_58])).

cnf(c_15884,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
    | r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15883])).

cnf(c_15887,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
    | r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_15884])).

cnf(c_15917,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15887,c_3703])).

cnf(c_15934,plain,
    ( r2_yellow_0(sK2,X0_52) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
    | r1_lattice3(sK2,X0_52,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15917,c_58])).

cnf(c_15935,plain,
    ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
    | r2_yellow_0(sK2,X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_15934])).

cnf(c_15938,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK4,sK5)),sK5) = iProver_top
    | r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9821,c_15935])).

cnf(c_3874,plain,
    ( ~ r1_lattice3(sK2,X0_52,sK5)
    | r1_lattice3(sK2,X1_52,sK5)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X0_52))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_10160,plain,
    ( r1_lattice3(sK2,X0_52,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3874])).

cnf(c_11901,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10160])).

cnf(c_11902,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
    | r1_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11901])).

cnf(c_28,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2942,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0_52))
    | ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4366,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_4372,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4366])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2941,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0_52),k1_zfmisc_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_4367,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_4370,plain,
    ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4367])).

cnf(c_3861,plain,
    ( r1_orders_2(sK2,sK5,X0_52)
    | ~ r1_lattice3(sK2,k1_tarski(X0_52),sK5)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_4275,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5))
    | ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3861])).

cnf(c_4288,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5)) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4275])).

cnf(c_4290,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK4,sK5)),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4288])).

cnf(c_3817,plain,
    ( r1_lattice3(sK2,X0_52,sK5)
    | r2_hidden(sK0(sK2,X0_52,sK5),X0_52)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_3818,plain,
    ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_52,sK5),X0_52) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3817])).

cnf(c_3820,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3818])).

cnf(c_3806,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5))
    | r1_lattice3(sK2,X0_52,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_3807,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5)) != iProver_top
    | r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3806])).

cnf(c_3809,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3807])).

cnf(c_3791,plain,
    ( r1_lattice3(sK2,X0_52,sK5)
    | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2919])).

cnf(c_3792,plain,
    ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3791])).

cnf(c_3794,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3792])).

cnf(c_60,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15938,c_11902,c_9772,c_4372,c_4370,c_4290,c_3820,c_3809,c_3794,c_60,c_58])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n015.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:50:23 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 7.54/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.49  
% 7.54/1.49  ------  iProver source info
% 7.54/1.49  
% 7.54/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.49  git: non_committed_changes: false
% 7.54/1.49  git: last_make_outside_of_git: false
% 7.54/1.49  
% 7.54/1.49  ------ 
% 7.54/1.49  
% 7.54/1.49  ------ Input Options
% 7.54/1.49  
% 7.54/1.49  --out_options                           all
% 7.54/1.49  --tptp_safe_out                         true
% 7.54/1.49  --problem_path                          ""
% 7.54/1.49  --include_path                          ""
% 7.54/1.49  --clausifier                            res/vclausify_rel
% 7.54/1.49  --clausifier_options                    ""
% 7.54/1.49  --stdin                                 false
% 7.54/1.49  --stats_out                             all
% 7.54/1.49  
% 7.54/1.49  ------ General Options
% 7.54/1.49  
% 7.54/1.49  --fof                                   false
% 7.54/1.49  --time_out_real                         305.
% 7.54/1.49  --time_out_virtual                      -1.
% 7.54/1.49  --symbol_type_check                     false
% 7.54/1.49  --clausify_out                          false
% 7.54/1.49  --sig_cnt_out                           false
% 7.54/1.49  --trig_cnt_out                          false
% 7.54/1.49  --trig_cnt_out_tolerance                1.
% 7.54/1.49  --trig_cnt_out_sk_spl                   false
% 7.54/1.49  --abstr_cl_out                          false
% 7.54/1.49  
% 7.54/1.49  ------ Global Options
% 7.54/1.49  
% 7.54/1.49  --schedule                              default
% 7.54/1.49  --add_important_lit                     false
% 7.54/1.49  --prop_solver_per_cl                    1000
% 7.54/1.49  --min_unsat_core                        false
% 7.54/1.49  --soft_assumptions                      false
% 7.54/1.49  --soft_lemma_size                       3
% 7.54/1.49  --prop_impl_unit_size                   0
% 7.54/1.49  --prop_impl_unit                        []
% 7.54/1.49  --share_sel_clauses                     true
% 7.54/1.49  --reset_solvers                         false
% 7.54/1.49  --bc_imp_inh                            [conj_cone]
% 7.54/1.49  --conj_cone_tolerance                   3.
% 7.54/1.49  --extra_neg_conj                        none
% 7.54/1.49  --large_theory_mode                     true
% 7.54/1.49  --prolific_symb_bound                   200
% 7.54/1.49  --lt_threshold                          2000
% 7.54/1.49  --clause_weak_htbl                      true
% 7.54/1.49  --gc_record_bc_elim                     false
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing Options
% 7.54/1.49  
% 7.54/1.49  --preprocessing_flag                    true
% 7.54/1.49  --time_out_prep_mult                    0.1
% 7.54/1.49  --splitting_mode                        input
% 7.54/1.49  --splitting_grd                         true
% 7.54/1.49  --splitting_cvd                         false
% 7.54/1.49  --splitting_cvd_svl                     false
% 7.54/1.49  --splitting_nvd                         32
% 7.54/1.49  --sub_typing                            true
% 7.54/1.49  --prep_gs_sim                           true
% 7.54/1.49  --prep_unflatten                        true
% 7.54/1.49  --prep_res_sim                          true
% 7.54/1.49  --prep_upred                            true
% 7.54/1.49  --prep_sem_filter                       exhaustive
% 7.54/1.49  --prep_sem_filter_out                   false
% 7.54/1.49  --pred_elim                             true
% 7.54/1.49  --res_sim_input                         true
% 7.54/1.49  --eq_ax_congr_red                       true
% 7.54/1.49  --pure_diseq_elim                       true
% 7.54/1.49  --brand_transform                       false
% 7.54/1.49  --non_eq_to_eq                          false
% 7.54/1.49  --prep_def_merge                        true
% 7.54/1.49  --prep_def_merge_prop_impl              false
% 7.54/1.49  --prep_def_merge_mbd                    true
% 7.54/1.49  --prep_def_merge_tr_red                 false
% 7.54/1.49  --prep_def_merge_tr_cl                  false
% 7.54/1.49  --smt_preprocessing                     true
% 7.54/1.49  --smt_ac_axioms                         fast
% 7.54/1.49  --preprocessed_out                      false
% 7.54/1.49  --preprocessed_stats                    false
% 7.54/1.49  
% 7.54/1.49  ------ Abstraction refinement Options
% 7.54/1.49  
% 7.54/1.49  --abstr_ref                             []
% 7.54/1.49  --abstr_ref_prep                        false
% 7.54/1.49  --abstr_ref_until_sat                   false
% 7.54/1.49  --abstr_ref_sig_restrict                funpre
% 7.54/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.49  --abstr_ref_under                       []
% 7.54/1.49  
% 7.54/1.49  ------ SAT Options
% 7.54/1.49  
% 7.54/1.49  --sat_mode                              false
% 7.54/1.49  --sat_fm_restart_options                ""
% 7.54/1.49  --sat_gr_def                            false
% 7.54/1.49  --sat_epr_types                         true
% 7.54/1.49  --sat_non_cyclic_types                  false
% 7.54/1.49  --sat_finite_models                     false
% 7.54/1.49  --sat_fm_lemmas                         false
% 7.54/1.49  --sat_fm_prep                           false
% 7.54/1.49  --sat_fm_uc_incr                        true
% 7.54/1.49  --sat_out_model                         small
% 7.54/1.49  --sat_out_clauses                       false
% 7.54/1.49  
% 7.54/1.49  ------ QBF Options
% 7.54/1.49  
% 7.54/1.49  --qbf_mode                              false
% 7.54/1.49  --qbf_elim_univ                         false
% 7.54/1.49  --qbf_dom_inst                          none
% 7.54/1.49  --qbf_dom_pre_inst                      false
% 7.54/1.49  --qbf_sk_in                             false
% 7.54/1.49  --qbf_pred_elim                         true
% 7.54/1.49  --qbf_split                             512
% 7.54/1.49  
% 7.54/1.49  ------ BMC1 Options
% 7.54/1.49  
% 7.54/1.49  --bmc1_incremental                      false
% 7.54/1.49  --bmc1_axioms                           reachable_all
% 7.54/1.49  --bmc1_min_bound                        0
% 7.54/1.49  --bmc1_max_bound                        -1
% 7.54/1.49  --bmc1_max_bound_default                -1
% 7.54/1.49  --bmc1_symbol_reachability              true
% 7.54/1.49  --bmc1_property_lemmas                  false
% 7.54/1.49  --bmc1_k_induction                      false
% 7.54/1.49  --bmc1_non_equiv_states                 false
% 7.54/1.49  --bmc1_deadlock                         false
% 7.54/1.49  --bmc1_ucm                              false
% 7.54/1.49  --bmc1_add_unsat_core                   none
% 7.54/1.49  --bmc1_unsat_core_children              false
% 7.54/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.49  --bmc1_out_stat                         full
% 7.54/1.49  --bmc1_ground_init                      false
% 7.54/1.49  --bmc1_pre_inst_next_state              false
% 7.54/1.49  --bmc1_pre_inst_state                   false
% 7.54/1.49  --bmc1_pre_inst_reach_state             false
% 7.54/1.49  --bmc1_out_unsat_core                   false
% 7.54/1.49  --bmc1_aig_witness_out                  false
% 7.54/1.49  --bmc1_verbose                          false
% 7.54/1.49  --bmc1_dump_clauses_tptp                false
% 7.54/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.49  --bmc1_dump_file                        -
% 7.54/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.49  --bmc1_ucm_extend_mode                  1
% 7.54/1.49  --bmc1_ucm_init_mode                    2
% 7.54/1.49  --bmc1_ucm_cone_mode                    none
% 7.54/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.49  --bmc1_ucm_relax_model                  4
% 7.54/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.49  --bmc1_ucm_layered_model                none
% 7.54/1.49  --bmc1_ucm_max_lemma_size               10
% 7.54/1.49  
% 7.54/1.49  ------ AIG Options
% 7.54/1.49  
% 7.54/1.49  --aig_mode                              false
% 7.54/1.49  
% 7.54/1.49  ------ Instantiation Options
% 7.54/1.49  
% 7.54/1.49  --instantiation_flag                    true
% 7.54/1.49  --inst_sos_flag                         true
% 7.54/1.49  --inst_sos_phase                        true
% 7.54/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.49  --inst_lit_sel_side                     num_symb
% 7.54/1.49  --inst_solver_per_active                1400
% 7.54/1.49  --inst_solver_calls_frac                1.
% 7.54/1.49  --inst_passive_queue_type               priority_queues
% 7.54/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.49  --inst_passive_queues_freq              [25;2]
% 7.54/1.49  --inst_dismatching                      true
% 7.54/1.49  --inst_eager_unprocessed_to_passive     true
% 7.54/1.49  --inst_prop_sim_given                   true
% 7.54/1.49  --inst_prop_sim_new                     false
% 7.54/1.49  --inst_subs_new                         false
% 7.54/1.49  --inst_eq_res_simp                      false
% 7.54/1.49  --inst_subs_given                       false
% 7.54/1.49  --inst_orphan_elimination               true
% 7.54/1.49  --inst_learning_loop_flag               true
% 7.54/1.49  --inst_learning_start                   3000
% 7.54/1.49  --inst_learning_factor                  2
% 7.54/1.49  --inst_start_prop_sim_after_learn       3
% 7.54/1.49  --inst_sel_renew                        solver
% 7.54/1.49  --inst_lit_activity_flag                true
% 7.54/1.49  --inst_restr_to_given                   false
% 7.54/1.49  --inst_activity_threshold               500
% 7.54/1.49  --inst_out_proof                        true
% 7.54/1.49  
% 7.54/1.49  ------ Resolution Options
% 7.54/1.49  
% 7.54/1.49  --resolution_flag                       true
% 7.54/1.49  --res_lit_sel                           adaptive
% 7.54/1.49  --res_lit_sel_side                      none
% 7.54/1.49  --res_ordering                          kbo
% 7.54/1.49  --res_to_prop_solver                    active
% 7.54/1.49  --res_prop_simpl_new                    false
% 7.54/1.49  --res_prop_simpl_given                  true
% 7.54/1.49  --res_passive_queue_type                priority_queues
% 7.54/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.49  --res_passive_queues_freq               [15;5]
% 7.54/1.49  --res_forward_subs                      full
% 7.54/1.49  --res_backward_subs                     full
% 7.54/1.49  --res_forward_subs_resolution           true
% 7.54/1.49  --res_backward_subs_resolution          true
% 7.54/1.49  --res_orphan_elimination                true
% 7.54/1.49  --res_time_limit                        2.
% 7.54/1.49  --res_out_proof                         true
% 7.54/1.49  
% 7.54/1.49  ------ Superposition Options
% 7.54/1.49  
% 7.54/1.49  --superposition_flag                    true
% 7.54/1.49  --sup_passive_queue_type                priority_queues
% 7.54/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.49  --demod_completeness_check              fast
% 7.54/1.49  --demod_use_ground                      true
% 7.54/1.49  --sup_to_prop_solver                    passive
% 7.54/1.49  --sup_prop_simpl_new                    true
% 7.54/1.49  --sup_prop_simpl_given                  true
% 7.54/1.49  --sup_fun_splitting                     true
% 7.54/1.49  --sup_smt_interval                      50000
% 7.54/1.49  
% 7.54/1.49  ------ Superposition Simplification Setup
% 7.54/1.49  
% 7.54/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.54/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.54/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.54/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.54/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.54/1.49  --sup_immed_triv                        [TrivRules]
% 7.54/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_immed_bw_main                     []
% 7.54/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.54/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_input_bw                          []
% 7.54/1.49  
% 7.54/1.49  ------ Combination Options
% 7.54/1.49  
% 7.54/1.49  --comb_res_mult                         3
% 7.54/1.49  --comb_sup_mult                         2
% 7.54/1.49  --comb_inst_mult                        10
% 7.54/1.49  
% 7.54/1.49  ------ Debug Options
% 7.54/1.49  
% 7.54/1.49  --dbg_backtrace                         false
% 7.54/1.49  --dbg_dump_prop_clauses                 false
% 7.54/1.49  --dbg_dump_prop_clauses_file            -
% 7.54/1.49  --dbg_out_stat                          false
% 7.54/1.49  ------ Parsing...
% 7.54/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  ------ Proving...
% 7.54/1.49  ------ Problem Properties 
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  clauses                                 31
% 7.54/1.49  conjectures                             8
% 7.54/1.49  EPR                                     2
% 7.54/1.49  Horn                                    23
% 7.54/1.49  unary                                   5
% 7.54/1.49  binary                                  4
% 7.54/1.49  lits                                    99
% 7.54/1.49  lits eq                                 8
% 7.54/1.49  fd_pure                                 0
% 7.54/1.49  fd_pseudo                               0
% 7.54/1.49  fd_cond                                 0
% 7.54/1.49  fd_pseudo_cond                          3
% 7.54/1.49  AC symbols                              0
% 7.54/1.49  
% 7.54/1.49  ------ Schedule dynamic 5 is on 
% 7.54/1.49  
% 7.54/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ 
% 7.54/1.49  Current options:
% 7.54/1.49  ------ 
% 7.54/1.49  
% 7.54/1.49  ------ Input Options
% 7.54/1.49  
% 7.54/1.49  --out_options                           all
% 7.54/1.49  --tptp_safe_out                         true
% 7.54/1.49  --problem_path                          ""
% 7.54/1.49  --include_path                          ""
% 7.54/1.49  --clausifier                            res/vclausify_rel
% 7.54/1.49  --clausifier_options                    ""
% 7.54/1.49  --stdin                                 false
% 7.54/1.49  --stats_out                             all
% 7.54/1.49  
% 7.54/1.49  ------ General Options
% 7.54/1.49  
% 7.54/1.49  --fof                                   false
% 7.54/1.49  --time_out_real                         305.
% 7.54/1.49  --time_out_virtual                      -1.
% 7.54/1.49  --symbol_type_check                     false
% 7.54/1.49  --clausify_out                          false
% 7.54/1.49  --sig_cnt_out                           false
% 7.54/1.49  --trig_cnt_out                          false
% 7.54/1.49  --trig_cnt_out_tolerance                1.
% 7.54/1.49  --trig_cnt_out_sk_spl                   false
% 7.54/1.49  --abstr_cl_out                          false
% 7.54/1.49  
% 7.54/1.49  ------ Global Options
% 7.54/1.49  
% 7.54/1.49  --schedule                              default
% 7.54/1.49  --add_important_lit                     false
% 7.54/1.49  --prop_solver_per_cl                    1000
% 7.54/1.49  --min_unsat_core                        false
% 7.54/1.49  --soft_assumptions                      false
% 7.54/1.49  --soft_lemma_size                       3
% 7.54/1.49  --prop_impl_unit_size                   0
% 7.54/1.49  --prop_impl_unit                        []
% 7.54/1.49  --share_sel_clauses                     true
% 7.54/1.49  --reset_solvers                         false
% 7.54/1.49  --bc_imp_inh                            [conj_cone]
% 7.54/1.49  --conj_cone_tolerance                   3.
% 7.54/1.49  --extra_neg_conj                        none
% 7.54/1.49  --large_theory_mode                     true
% 7.54/1.49  --prolific_symb_bound                   200
% 7.54/1.49  --lt_threshold                          2000
% 7.54/1.49  --clause_weak_htbl                      true
% 7.54/1.49  --gc_record_bc_elim                     false
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing Options
% 7.54/1.49  
% 7.54/1.49  --preprocessing_flag                    true
% 7.54/1.49  --time_out_prep_mult                    0.1
% 7.54/1.49  --splitting_mode                        input
% 7.54/1.49  --splitting_grd                         true
% 7.54/1.49  --splitting_cvd                         false
% 7.54/1.49  --splitting_cvd_svl                     false
% 7.54/1.49  --splitting_nvd                         32
% 7.54/1.49  --sub_typing                            true
% 7.54/1.49  --prep_gs_sim                           true
% 7.54/1.49  --prep_unflatten                        true
% 7.54/1.49  --prep_res_sim                          true
% 7.54/1.49  --prep_upred                            true
% 7.54/1.49  --prep_sem_filter                       exhaustive
% 7.54/1.49  --prep_sem_filter_out                   false
% 7.54/1.49  --pred_elim                             true
% 7.54/1.49  --res_sim_input                         true
% 7.54/1.49  --eq_ax_congr_red                       true
% 7.54/1.49  --pure_diseq_elim                       true
% 7.54/1.49  --brand_transform                       false
% 7.54/1.49  --non_eq_to_eq                          false
% 7.54/1.49  --prep_def_merge                        true
% 7.54/1.49  --prep_def_merge_prop_impl              false
% 7.54/1.49  --prep_def_merge_mbd                    true
% 7.54/1.49  --prep_def_merge_tr_red                 false
% 7.54/1.49  --prep_def_merge_tr_cl                  false
% 7.54/1.49  --smt_preprocessing                     true
% 7.54/1.49  --smt_ac_axioms                         fast
% 7.54/1.49  --preprocessed_out                      false
% 7.54/1.49  --preprocessed_stats                    false
% 7.54/1.49  
% 7.54/1.49  ------ Abstraction refinement Options
% 7.54/1.49  
% 7.54/1.49  --abstr_ref                             []
% 7.54/1.49  --abstr_ref_prep                        false
% 7.54/1.49  --abstr_ref_until_sat                   false
% 7.54/1.49  --abstr_ref_sig_restrict                funpre
% 7.54/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.49  --abstr_ref_under                       []
% 7.54/1.49  
% 7.54/1.49  ------ SAT Options
% 7.54/1.49  
% 7.54/1.49  --sat_mode                              false
% 7.54/1.49  --sat_fm_restart_options                ""
% 7.54/1.49  --sat_gr_def                            false
% 7.54/1.49  --sat_epr_types                         true
% 7.54/1.49  --sat_non_cyclic_types                  false
% 7.54/1.49  --sat_finite_models                     false
% 7.54/1.49  --sat_fm_lemmas                         false
% 7.54/1.49  --sat_fm_prep                           false
% 7.54/1.49  --sat_fm_uc_incr                        true
% 7.54/1.49  --sat_out_model                         small
% 7.54/1.49  --sat_out_clauses                       false
% 7.54/1.49  
% 7.54/1.49  ------ QBF Options
% 7.54/1.49  
% 7.54/1.49  --qbf_mode                              false
% 7.54/1.49  --qbf_elim_univ                         false
% 7.54/1.49  --qbf_dom_inst                          none
% 7.54/1.49  --qbf_dom_pre_inst                      false
% 7.54/1.49  --qbf_sk_in                             false
% 7.54/1.49  --qbf_pred_elim                         true
% 7.54/1.49  --qbf_split                             512
% 7.54/1.49  
% 7.54/1.49  ------ BMC1 Options
% 7.54/1.49  
% 7.54/1.49  --bmc1_incremental                      false
% 7.54/1.49  --bmc1_axioms                           reachable_all
% 7.54/1.49  --bmc1_min_bound                        0
% 7.54/1.49  --bmc1_max_bound                        -1
% 7.54/1.49  --bmc1_max_bound_default                -1
% 7.54/1.49  --bmc1_symbol_reachability              true
% 7.54/1.49  --bmc1_property_lemmas                  false
% 7.54/1.49  --bmc1_k_induction                      false
% 7.54/1.49  --bmc1_non_equiv_states                 false
% 7.54/1.49  --bmc1_deadlock                         false
% 7.54/1.49  --bmc1_ucm                              false
% 7.54/1.49  --bmc1_add_unsat_core                   none
% 7.54/1.49  --bmc1_unsat_core_children              false
% 7.54/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.49  --bmc1_out_stat                         full
% 7.54/1.49  --bmc1_ground_init                      false
% 7.54/1.49  --bmc1_pre_inst_next_state              false
% 7.54/1.49  --bmc1_pre_inst_state                   false
% 7.54/1.49  --bmc1_pre_inst_reach_state             false
% 7.54/1.49  --bmc1_out_unsat_core                   false
% 7.54/1.49  --bmc1_aig_witness_out                  false
% 7.54/1.49  --bmc1_verbose                          false
% 7.54/1.49  --bmc1_dump_clauses_tptp                false
% 7.54/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.49  --bmc1_dump_file                        -
% 7.54/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.49  --bmc1_ucm_extend_mode                  1
% 7.54/1.49  --bmc1_ucm_init_mode                    2
% 7.54/1.49  --bmc1_ucm_cone_mode                    none
% 7.54/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.49  --bmc1_ucm_relax_model                  4
% 7.54/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.49  --bmc1_ucm_layered_model                none
% 7.54/1.49  --bmc1_ucm_max_lemma_size               10
% 7.54/1.49  
% 7.54/1.49  ------ AIG Options
% 7.54/1.49  
% 7.54/1.49  --aig_mode                              false
% 7.54/1.49  
% 7.54/1.49  ------ Instantiation Options
% 7.54/1.49  
% 7.54/1.49  --instantiation_flag                    true
% 7.54/1.49  --inst_sos_flag                         true
% 7.54/1.49  --inst_sos_phase                        true
% 7.54/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.49  --inst_lit_sel_side                     none
% 7.54/1.49  --inst_solver_per_active                1400
% 7.54/1.49  --inst_solver_calls_frac                1.
% 7.54/1.49  --inst_passive_queue_type               priority_queues
% 7.54/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.49  --inst_passive_queues_freq              [25;2]
% 7.54/1.49  --inst_dismatching                      true
% 7.54/1.49  --inst_eager_unprocessed_to_passive     true
% 7.54/1.49  --inst_prop_sim_given                   true
% 7.54/1.49  --inst_prop_sim_new                     false
% 7.54/1.49  --inst_subs_new                         false
% 7.54/1.49  --inst_eq_res_simp                      false
% 7.54/1.49  --inst_subs_given                       false
% 7.54/1.49  --inst_orphan_elimination               true
% 7.54/1.49  --inst_learning_loop_flag               true
% 7.54/1.49  --inst_learning_start                   3000
% 7.54/1.49  --inst_learning_factor                  2
% 7.54/1.49  --inst_start_prop_sim_after_learn       3
% 7.54/1.49  --inst_sel_renew                        solver
% 7.54/1.49  --inst_lit_activity_flag                true
% 7.54/1.49  --inst_restr_to_given                   false
% 7.54/1.49  --inst_activity_threshold               500
% 7.54/1.49  --inst_out_proof                        true
% 7.54/1.49  
% 7.54/1.49  ------ Resolution Options
% 7.54/1.49  
% 7.54/1.49  --resolution_flag                       false
% 7.54/1.49  --res_lit_sel                           adaptive
% 7.54/1.49  --res_lit_sel_side                      none
% 7.54/1.49  --res_ordering                          kbo
% 7.54/1.49  --res_to_prop_solver                    active
% 7.54/1.49  --res_prop_simpl_new                    false
% 7.54/1.49  --res_prop_simpl_given                  true
% 7.54/1.49  --res_passive_queue_type                priority_queues
% 7.54/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.49  --res_passive_queues_freq               [15;5]
% 7.54/1.49  --res_forward_subs                      full
% 7.54/1.49  --res_backward_subs                     full
% 7.54/1.49  --res_forward_subs_resolution           true
% 7.54/1.49  --res_backward_subs_resolution          true
% 7.54/1.49  --res_orphan_elimination                true
% 7.54/1.49  --res_time_limit                        2.
% 7.54/1.49  --res_out_proof                         true
% 7.54/1.49  
% 7.54/1.49  ------ Superposition Options
% 7.54/1.49  
% 7.54/1.49  --superposition_flag                    true
% 7.54/1.49  --sup_passive_queue_type                priority_queues
% 7.54/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.49  --demod_completeness_check              fast
% 7.54/1.49  --demod_use_ground                      true
% 7.54/1.49  --sup_to_prop_solver                    passive
% 7.54/1.49  --sup_prop_simpl_new                    true
% 7.54/1.49  --sup_prop_simpl_given                  true
% 7.54/1.49  --sup_fun_splitting                     true
% 7.54/1.49  --sup_smt_interval                      50000
% 7.54/1.49  
% 7.54/1.49  ------ Superposition Simplification Setup
% 7.54/1.49  
% 7.54/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.54/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.54/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.54/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.54/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.54/1.49  --sup_immed_triv                        [TrivRules]
% 7.54/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_immed_bw_main                     []
% 7.54/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.54/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.49  --sup_input_bw                          []
% 7.54/1.49  
% 7.54/1.49  ------ Combination Options
% 7.54/1.49  
% 7.54/1.49  --comb_res_mult                         3
% 7.54/1.49  --comb_sup_mult                         2
% 7.54/1.49  --comb_inst_mult                        10
% 7.54/1.49  
% 7.54/1.49  ------ Debug Options
% 7.54/1.49  
% 7.54/1.49  --dbg_backtrace                         false
% 7.54/1.49  --dbg_dump_prop_clauses                 false
% 7.54/1.49  --dbg_dump_prop_clauses_file            -
% 7.54/1.49  --dbg_out_stat                          false
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS status Theorem for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  fof(f12,conjecture,(
% 7.54/1.49    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f13,negated_conjecture,(
% 7.54/1.49    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 7.54/1.49    inference(negated_conjecture,[],[f12])).
% 7.54/1.49  
% 7.54/1.49  fof(f14,plain,(
% 7.54/1.49    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 7.54/1.49    inference(rectify,[],[f13])).
% 7.54/1.49  
% 7.54/1.49  fof(f16,plain,(
% 7.54/1.49    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 7.54/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.54/1.49  
% 7.54/1.49  fof(f17,plain,(
% 7.54/1.49    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 7.54/1.49    inference(pure_predicate_removal,[],[f16])).
% 7.54/1.49  
% 7.54/1.49  fof(f29,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f17])).
% 7.54/1.49  
% 7.54/1.49  fof(f30,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f29])).
% 7.54/1.49  
% 7.54/1.49  fof(f40,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 7.54/1.49    inference(nnf_transformation,[],[f30])).
% 7.54/1.49  
% 7.54/1.49  fof(f41,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f40])).
% 7.54/1.49  
% 7.54/1.49  fof(f42,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 7.54/1.49    inference(rectify,[],[f41])).
% 7.54/1.49  
% 7.54/1.49  fof(f47,plain,(
% 7.54/1.49    ( ! [X0,X1] : (! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k2_yellow_0(X0,sK6(X5)) = X5 & r2_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f46,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r1_lattice3(X0,X2,sK5) | ~r1_lattice3(X0,X1,sK5)) & (r1_lattice3(X0,X2,sK5) | r1_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f45,plain,(
% 7.54/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r1_lattice3(X0,sK4,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,sK4,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f44,plain,(
% 7.54/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,sK3,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f43,plain,(
% 7.54/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK2,X2,X3) | ~r1_lattice3(sK2,X1,X3)) & (r1_lattice3(sK2,X2,X3) | r1_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK2,X6) = X5 & r2_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f48,plain,(
% 7.54/1.49    ((((~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)) & (r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK2,sK6(X5)) = X5 & r2_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f42,f47,f46,f45,f44,f43])).
% 7.54/1.49  
% 7.54/1.49  fof(f82,plain,(
% 7.54/1.49    m1_subset_1(sK5,u1_struct_0(sK2))),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f6,axiom,(
% 7.54/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f20,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f6])).
% 7.54/1.49  
% 7.54/1.49  fof(f21,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f20])).
% 7.54/1.49  
% 7.54/1.49  fof(f31,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(nnf_transformation,[],[f21])).
% 7.54/1.49  
% 7.54/1.49  fof(f32,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(rectify,[],[f31])).
% 7.54/1.49  
% 7.54/1.49  fof(f33,plain,(
% 7.54/1.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f34,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.54/1.49  
% 7.54/1.49  fof(f56,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f34])).
% 7.54/1.49  
% 7.54/1.49  fof(f73,plain,(
% 7.54/1.49    l1_orders_2(sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f55,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f34])).
% 7.54/1.49  
% 7.54/1.49  fof(f80,plain,(
% 7.54/1.49    ( ! [X5] : (k2_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f3,axiom,(
% 7.54/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f18,plain,(
% 7.54/1.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 7.54/1.49    inference(ennf_transformation,[],[f3])).
% 7.54/1.49  
% 7.54/1.49  fof(f51,plain,(
% 7.54/1.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f18])).
% 7.54/1.49  
% 7.54/1.49  fof(f5,axiom,(
% 7.54/1.49    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f53,plain,(
% 7.54/1.49    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f5])).
% 7.54/1.49  
% 7.54/1.49  fof(f81,plain,(
% 7.54/1.49    ( ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f8,axiom,(
% 7.54/1.49    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f24,plain,(
% 7.54/1.49    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f8])).
% 7.54/1.49  
% 7.54/1.49  fof(f63,plain,(
% 7.54/1.49    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f24])).
% 7.54/1.49  
% 7.54/1.49  fof(f1,axiom,(
% 7.54/1.49    v1_xboole_0(k1_xboole_0)),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f49,plain,(
% 7.54/1.49    v1_xboole_0(k1_xboole_0)),
% 7.54/1.49    inference(cnf_transformation,[],[f1])).
% 7.54/1.49  
% 7.54/1.49  fof(f2,axiom,(
% 7.54/1.49    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f50,plain,(
% 7.54/1.49    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f2])).
% 7.54/1.49  
% 7.54/1.49  fof(f4,axiom,(
% 7.54/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f15,plain,(
% 7.54/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.54/1.49    inference(unused_predicate_definition_removal,[],[f4])).
% 7.54/1.49  
% 7.54/1.49  fof(f19,plain,(
% 7.54/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.54/1.49    inference(ennf_transformation,[],[f15])).
% 7.54/1.49  
% 7.54/1.49  fof(f52,plain,(
% 7.54/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f19])).
% 7.54/1.49  
% 7.54/1.49  fof(f11,axiom,(
% 7.54/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f28,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f11])).
% 7.54/1.49  
% 7.54/1.49  fof(f70,plain,(
% 7.54/1.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f28])).
% 7.54/1.49  
% 7.54/1.49  fof(f83,plain,(
% 7.54/1.49    r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f76,plain,(
% 7.54/1.49    ( ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f54,plain,(
% 7.54/1.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f34])).
% 7.54/1.49  
% 7.54/1.49  fof(f7,axiom,(
% 7.54/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f22,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f7])).
% 7.54/1.49  
% 7.54/1.49  fof(f23,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f22])).
% 7.54/1.49  
% 7.54/1.49  fof(f35,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(nnf_transformation,[],[f23])).
% 7.54/1.49  
% 7.54/1.49  fof(f36,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f35])).
% 7.54/1.49  
% 7.54/1.49  fof(f37,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(rectify,[],[f36])).
% 7.54/1.49  
% 7.54/1.49  fof(f38,plain,(
% 7.54/1.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f39,plain,(
% 7.54/1.49    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.54/1.49  
% 7.54/1.49  fof(f58,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f39])).
% 7.54/1.49  
% 7.54/1.49  fof(f86,plain,(
% 7.54/1.49    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(equality_resolution,[],[f58])).
% 7.54/1.49  
% 7.54/1.49  fof(f9,axiom,(
% 7.54/1.49    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f25,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f9])).
% 7.54/1.49  
% 7.54/1.49  fof(f26,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 7.54/1.49    inference(flattening,[],[f25])).
% 7.54/1.49  
% 7.54/1.49  fof(f64,plain,(
% 7.54/1.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f26])).
% 7.54/1.49  
% 7.54/1.49  fof(f72,plain,(
% 7.54/1.49    v4_orders_2(sK2)),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f10,axiom,(
% 7.54/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 7.54/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f27,plain,(
% 7.54/1.49    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f10])).
% 7.54/1.49  
% 7.54/1.49  fof(f66,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f57,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f34])).
% 7.54/1.49  
% 7.54/1.49  fof(f84,plain,(
% 7.54/1.49    ~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f59,plain,(
% 7.54/1.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f39])).
% 7.54/1.49  
% 7.54/1.49  fof(f85,plain,(
% 7.54/1.49    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(equality_resolution,[],[f59])).
% 7.54/1.49  
% 7.54/1.49  fof(f67,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f27])).
% 7.54/1.49  
% 7.54/1.49  fof(f79,plain,(
% 7.54/1.49    ( ! [X5] : (r2_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f78,plain,(
% 7.54/1.49    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  cnf(c_25,negated_conjecture,
% 7.54/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2944,negated_conjecture,
% 7.54/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3677,plain,
% 7.54/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2944]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_34,negated_conjecture,
% 7.54/1.49      ( l1_orders_2(sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_899,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_900,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0,X1)
% 7.54/1.49      | r2_hidden(sK0(sK2,X0,X1),X0)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_899]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2918,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,X1_52)
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52)
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_900]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3702,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,X1_52),X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2918]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_7,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,X2)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_884,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,X2)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_885,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0,X1)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_884]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2919,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,X1_52)
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_885]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3701,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0_52,X1_52),u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2919]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_27,negated_conjecture,
% 7.54/1.49      ( ~ r2_hidden(X0,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | k2_yellow_0(sK2,sK6(X0)) = X0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2943,negated_conjecture,
% 7.54/1.49      ( ~ r2_hidden(X0_52,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | k2_yellow_0(sK2,sK6(X0_52)) = X0_52 ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_27]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3678,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(X0_52)) = X0_52
% 7.54/1.49      | r2_hidden(X0_52,sK4) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2943]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5282,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(sK0(sK2,X0_52,X1_52))) = sK0(sK2,X0_52,X1_52)
% 7.54/1.49      | r1_lattice3(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,X1_52),sK4) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3701,c_3678]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5863,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_52))) = sK0(sK2,sK4,X0_52)
% 7.54/1.49      | r1_lattice3(sK2,sK4,X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3702,c_5282]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6364,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3677,c_5863]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2,plain,
% 7.54/1.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2947,plain,
% 7.54/1.49      ( ~ r2_hidden(X0_52,X1_52)
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3674,plain,
% 7.54/1.49      ( r2_hidden(X0_52,X1_52) != iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(X1_52)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2947]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4,plain,
% 7.54/1.49      ( v1_finset_1(k1_tarski(X0)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_26,negated_conjecture,
% 7.54/1.49      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 7.54/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.54/1.49      | ~ v1_finset_1(X0)
% 7.54/1.49      | k1_xboole_0 = X0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_599,plain,
% 7.54/1.49      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 7.54/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_tarski(X1) != X0
% 7.54/1.49      | k1_xboole_0 = X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_600,plain,
% 7.54/1.49      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
% 7.54/1.49      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_xboole_0 = k1_tarski(X0) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_599]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2934,plain,
% 7.54/1.49      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_52)),sK4)
% 7.54/1.49      | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_xboole_0 = k1_tarski(X0_52) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_600]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3686,plain,
% 7.54/1.49      ( k1_xboole_0 = k1_tarski(X0_52)
% 7.54/1.49      | r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_52)),sK4) = iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2934]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_14,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_769,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_770,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_769]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2925,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_770]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3695,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2925]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4213,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,X0_52))) = k2_yellow_0(sK2,X0_52)
% 7.54/1.49      | r2_hidden(k2_yellow_0(sK2,X0_52),sK4) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3695,c_3678]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5240,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
% 7.54/1.49      | k1_tarski(X0_52) = k1_xboole_0
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3686,c_4213]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_0,plain,
% 7.54/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_1,plain,
% 7.54/1.49      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_470,plain,
% 7.54/1.49      ( k1_tarski(X0) != k1_xboole_0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2938,plain,
% 7.54/1.49      ( k1_tarski(X0_52) != k1_xboole_0 ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_470]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6293,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_5240,c_2938]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6299,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(X0_52)))) = k2_yellow_0(sK2,k1_tarski(X0_52))
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3674,c_6293]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6359,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_52)))
% 7.54/1.49      | r1_lattice3(sK2,sK3,X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3702,c_6299]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_7993,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 7.54/1.49      | r1_lattice3(sK2,sK3,sK5) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3677,c_6359]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3,plain,
% 7.54/1.49      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_22,plain,
% 7.54/1.49      ( ~ r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X2)
% 7.54/1.49      | ~ r1_tarski(X3,X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_476,plain,
% 7.54/1.49      ( ~ r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X2)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.54/1.49      | ~ l1_orders_2(X0)
% 7.54/1.49      | X3 != X4
% 7.54/1.49      | X1 != X5 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_477,plain,
% 7.54/1.49      ( ~ r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X2)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_476]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_669,plain,
% 7.54/1.49      ( ~ r1_lattice3(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X2)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_477,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_670,plain,
% 7.54/1.49      ( ~ r1_lattice3(sK2,X0,X1)
% 7.54/1.49      | r1_lattice3(sK2,X2,X1)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_669]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2931,plain,
% 7.54/1.49      ( ~ r1_lattice3(sK2,X0_52,X1_52)
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X1_52)
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_670]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3689,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,X1_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X1_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2931]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4626,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(X0_52)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3677,c_3689]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8045,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_7993,c_4626]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8692,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))))) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3674,c_8045]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3778,plain,
% 7.54/1.49      ( ~ r2_hidden(X0_52,sK3)
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2947]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3779,plain,
% 7.54/1.49      ( r2_hidden(X0_52,sK3) != iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_3778]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_24,negated_conjecture,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 7.54/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2945,negated_conjecture,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3676,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2945]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4668,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3676,c_4626]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4971,plain,
% 7.54/1.49      ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3674,c_4668]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_31,negated_conjecture,
% 7.54/1.49      ( r2_yellow_0(sK2,X0)
% 7.54/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.54/1.49      | ~ v1_finset_1(X0)
% 7.54/1.49      | k1_xboole_0 = X0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_584,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,X0)
% 7.54/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_tarski(X1) != X0
% 7.54/1.49      | k1_xboole_0 = X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_31]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_585,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,k1_tarski(X0))
% 7.54/1.49      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_xboole_0 = k1_tarski(X0) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_584]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2935,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,k1_tarski(X0_52))
% 7.54/1.49      | ~ m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3))
% 7.54/1.49      | k1_xboole_0 = k1_tarski(X0_52) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_585]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3685,plain,
% 7.54/1.49      ( k1_xboole_0 = k1_tarski(X0_52)
% 7.54/1.49      | r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2935]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5235,plain,
% 7.54/1.49      ( k1_tarski(X0_52) = k1_xboole_0
% 7.54/1.49      | r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3674,c_3685]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5815,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,k1_tarski(X0_52)) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_5235,c_2938]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,X3,X1)
% 7.54/1.49      | ~ r2_hidden(X2,X3)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_863,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,X3,X1)
% 7.54/1.49      | ~ r2_hidden(X2,X3)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_864,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0,X1)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2,X0)
% 7.54/1.49      | ~ r2_hidden(X1,X2)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_863]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2920,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2_52,X0_52)
% 7.54/1.49      | ~ r2_hidden(X1_52,X2_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_864]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3700,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X0_52) != iProver_top
% 7.54/1.49      | r2_hidden(X1_52,X2_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2920]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4806,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) != iProver_top
% 7.54/1.49      | r2_hidden(X0_52,X1_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3677,c_3700]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4864,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) != iProver_top
% 7.54/1.49      | r2_hidden(k2_yellow_0(sK2,X0_52),X1_52) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3695,c_4806]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5942,plain,
% 7.54/1.49      ( k1_tarski(X0_52) = k1_xboole_0
% 7.54/1.49      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0_52))) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3686,c_4864]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8425,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,k1_tarski(X0_52))) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_5942,c_2938]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_13,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 7.54/1.49      | ~ r2_yellow_0(X0,X1)
% 7.54/1.49      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_215,plain,
% 7.54/1.49      ( ~ r2_yellow_0(X0,X1)
% 7.54/1.49      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_13,c_14]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_216,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 7.54/1.49      | ~ r2_yellow_0(X0,X1)
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_215]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_685,plain,
% 7.54/1.49      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 7.54/1.49      | ~ r2_yellow_0(X0,X1)
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_216,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_686,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) | ~ r2_yellow_0(sK2,X0) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_685]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2930,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52))
% 7.54/1.49      | ~ r2_yellow_0(sK2,X0_52) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_686]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3690,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52)) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2930]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_16,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,X3,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ v4_orders_2(X0)
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_35,negated_conjecture,
% 7.54/1.49      ( v4_orders_2(sK2) ),
% 7.54/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_526,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,X3,X2)
% 7.54/1.49      | r1_lattice3(X0,X3,X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0)
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_527,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0,X1)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2,X1)
% 7.54/1.49      | r1_lattice3(sK2,X2,X0)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.54/1.49      | ~ l1_orders_2(sK2) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_526]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_529,plain,
% 7.54/1.49      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | r1_lattice3(sK2,X2,X0)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2,X1)
% 7.54/1.49      | ~ r1_orders_2(sK2,X0,X1) ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_527,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_530,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0,X1)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2,X1)
% 7.54/1.49      | r1_lattice3(sK2,X2,X0)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_529]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2937,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0_52,X1_52)
% 7.54/1.49      | ~ r1_lattice3(sK2,X2_52,X1_52)
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X0_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_530]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3683,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X1_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X2_52,X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2937]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4532,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3677,c_3683]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4621,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,k2_yellow_0(sK2,X0_52)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3695,c_4532]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6143,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,k2_yellow_0(sK2,X0_52)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3690,c_4621]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8433,plain,
% 7.54/1.49      ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) != iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,k1_tarski(X0_52)) != iProver_top
% 7.54/1.49      | m1_subset_1(k1_tarski(X0_52),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_8425,c_6143]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8778,plain,
% 7.54/1.49      ( r1_lattice3(sK2,k1_tarski(X0_52),sK5) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_8692,c_3779,c_4971,c_5815,c_8433]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_697,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,X2)
% 7.54/1.49      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_698,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0,X1)
% 7.54/1.49      | ~ r1_lattice3(sK2,k1_tarski(X1),X0)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_697]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2929,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52)
% 7.54/1.49      | ~ r1_lattice3(sK2,k1_tarski(X1_52),X0_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_698]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3691,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2929]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_8784,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_8778,c_3691]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_58,plain,
% 7.54/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9024,plain,
% 7.54/1.49      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top
% 7.54/1.49      | r1_orders_2(sK2,sK5,X0_52) = iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_8784,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9025,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) = iProver_top
% 7.54/1.49      | r2_hidden(X0_52,sK3) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_9024]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9031,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,X1_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,X1_52) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,X1_52),sK3) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3701,c_9025]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 7.54/1.49      | r1_lattice3(X0,X2,X1)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_914,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 7.54/1.49      | r1_lattice3(X0,X2,X1)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_915,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 7.54/1.49      | r1_lattice3(sK2,X1,X0)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_914]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2917,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0_52,sK0(sK2,X1_52,X0_52))
% 7.54/1.49      | r1_lattice3(sK2,X1_52,X0_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_915]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3703,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,sK0(sK2,X1_52,X0_52)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2917]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9738,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_9031,c_3703]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9766,plain,
% 7.54/1.49      ( r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) = iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_9738,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9767,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,sK5),sK3) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_9766]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9772,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3702,c_9767]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9775,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) = iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_9772,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_23,negated_conjecture,
% 7.54/1.49      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 7.54/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2946,negated_conjecture,
% 7.54/1.49      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3675,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2946]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9779,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_9775,c_3675]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9821,plain,
% 7.54/1.49      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_6364,c_9779]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_12,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 7.54/1.49      | ~ r1_lattice3(X0,X2,X1)
% 7.54/1.49      | ~ r2_yellow_0(X0,X2)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_778,plain,
% 7.54/1.49      ( r1_orders_2(X0,X1,k2_yellow_0(X0,X2))
% 7.54/1.49      | ~ r1_lattice3(X0,X2,X1)
% 7.54/1.49      | ~ r2_yellow_0(X0,X2)
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_779,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
% 7.54/1.49      | ~ r1_lattice3(sK2,X1,X0)
% 7.54/1.49      | ~ r2_yellow_0(sK2,X1)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(k2_yellow_0(sK2,X1),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_778]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_788,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0,k2_yellow_0(sK2,X1))
% 7.54/1.49      | ~ r1_lattice3(sK2,X1,X0)
% 7.54/1.49      | ~ r2_yellow_0(sK2,X1)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(forward_subsumption_resolution,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_779,c_770]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2924,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,k2_yellow_0(sK2,X1_52))
% 7.54/1.49      | ~ r1_lattice3(sK2,X1_52,X0_52)
% 7.54/1.49      | ~ r2_yellow_0(sK2,X1_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_788]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3696,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,k2_yellow_0(sK2,X1_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,X0_52) != iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X1_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_19,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,k1_tarski(X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | ~ l1_orders_2(X0) ),
% 7.54/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_715,plain,
% 7.54/1.49      ( ~ r1_orders_2(X0,X1,X2)
% 7.54/1.49      | r1_lattice3(X0,k1_tarski(X2),X1)
% 7.54/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.49      | sK2 != X0 ),
% 7.54/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_716,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0,X1)
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1),X0)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(unflattening,[status(thm)],[c_715]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2928,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,X0_52,X1_52)
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),X0_52)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(X1_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_716]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3692,plain,
% 7.54/1.49      ( r1_orders_2(sK2,X0_52,X1_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2928]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4758,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3692,c_4626]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6621,plain,
% 7.54/1.49      ( m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top
% 7.54/1.49      | r1_orders_2(sK2,sK5,X0_52) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_4758,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6622,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k1_tarski(X0_52))) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_6621]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6627,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
% 7.54/1.49      | r2_hidden(X1_52,k1_tarski(X0_52)) != iProver_top
% 7.54/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3674,c_6622]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_6632,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | r2_hidden(X1_52,k1_tarski(k2_yellow_0(sK2,X0_52))) != iProver_top
% 7.54/1.49      | m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3696,c_6627]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3015,plain,
% 7.54/1.49      ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_2925]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_12369,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(X1_52),sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | r2_hidden(X1_52,k1_tarski(k2_yellow_0(sK2,X0_52))) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_6632,c_58,c_3015]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_12373,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)),sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3702,c_12369]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_12447,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_12373,c_3691]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15883,plain,
% 7.54/1.49      ( m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_12447,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15884,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52),u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_15883]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15887,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),X1_52) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3701,c_15884]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15917,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_15887,c_3703]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15934,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,X0_52) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_15917,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15935,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(k2_yellow_0(sK2,X0_52)),sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,X0_52) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_15934]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_15938,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK4,sK5)),sK5) = iProver_top
% 7.54/1.49      | r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_9821,c_15935]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3874,plain,
% 7.54/1.49      ( ~ r1_lattice3(sK2,X0_52,sK5)
% 7.54/1.49      | r1_lattice3(sK2,X1_52,sK5)
% 7.54/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(X0_52))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2931]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_10160,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5)
% 7.54/1.49      | ~ r1_lattice3(sK2,sK3,sK5)
% 7.54/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK3))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3874]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_11901,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 7.54/1.49      | ~ r1_lattice3(sK2,sK3,sK5)
% 7.54/1.49      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_10160]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_11902,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK3,sK5) != iProver_top
% 7.54/1.49      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_11901]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_28,negated_conjecture,
% 7.54/1.49      ( r2_yellow_0(sK2,sK6(X0))
% 7.54/1.49      | ~ r2_hidden(X0,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2942,negated_conjecture,
% 7.54/1.49      ( r2_yellow_0(sK2,sK6(X0_52))
% 7.54/1.49      | ~ r2_hidden(X0_52,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4366,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 7.54/1.49      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 7.54/1.49      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2942]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4372,plain,
% 7.54/1.49      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_4366]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_29,negated_conjecture,
% 7.54/1.49      ( ~ r2_hidden(X0,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.54/1.49      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2941,negated_conjecture,
% 7.54/1.49      ( ~ r2_hidden(X0_52,sK4)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | m1_subset_1(sK6(X0_52),k1_zfmisc_1(sK3)) ),
% 7.54/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4367,plain,
% 7.54/1.49      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 7.54/1.49      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 7.54/1.49      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2941]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4370,plain,
% 7.54/1.49      ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_4367]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3861,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,X0_52)
% 7.54/1.49      | ~ r1_lattice3(sK2,k1_tarski(X0_52),sK5)
% 7.54/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2929]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4275,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5))
% 7.54/1.49      | ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5)
% 7.54/1.49      | ~ m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3861]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4288,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(sK0(sK2,X0_52,sK5)),sK5) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_4275]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4290,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) = iProver_top
% 7.54/1.49      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK4,sK5)),sK5) != iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_4288]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3817,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5)
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,sK5),X0_52)
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2918]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3818,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,X0_52,sK5),X0_52) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_3817]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3820,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 7.54/1.49      | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3818]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3806,plain,
% 7.54/1.49      ( ~ r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5))
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5)
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2917]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3807,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,X0_52,sK5)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_3806]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3809,plain,
% 7.54/1.49      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3807]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3791,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5)
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2))
% 7.54/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2919]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3792,plain,
% 7.54/1.49      ( r1_lattice3(sK2,X0_52,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,X0_52,sK5),u1_struct_0(sK2)) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_3791]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3794,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK4,sK5) = iProver_top
% 7.54/1.49      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
% 7.54/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_3792]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_60,plain,
% 7.54/1.49      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 7.54/1.49      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(contradiction,plain,
% 7.54/1.49      ( $false ),
% 7.54/1.49      inference(minisat,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_15938,c_11902,c_9772,c_4372,c_4370,c_4290,c_3820,
% 7.54/1.49                 c_3809,c_3794,c_60,c_58]) ).
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  ------                               Statistics
% 7.54/1.49  
% 7.54/1.49  ------ General
% 7.54/1.49  
% 7.54/1.49  abstr_ref_over_cycles:                  0
% 7.54/1.49  abstr_ref_under_cycles:                 0
% 7.54/1.49  gc_basic_clause_elim:                   0
% 7.54/1.49  forced_gc_time:                         0
% 7.54/1.49  parsing_time:                           0.017
% 7.54/1.49  unif_index_cands_time:                  0.
% 7.54/1.49  unif_index_add_time:                    0.
% 7.54/1.49  orderings_time:                         0.
% 7.54/1.49  out_proof_time:                         0.017
% 7.54/1.49  total_time:                             0.564
% 7.54/1.49  num_of_symbols:                         53
% 7.54/1.49  num_of_terms:                           13146
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing
% 7.54/1.49  
% 7.54/1.49  num_of_splits:                          0
% 7.54/1.49  num_of_split_atoms:                     0
% 7.54/1.49  num_of_reused_defs:                     0
% 7.54/1.49  num_eq_ax_congr_red:                    35
% 7.54/1.49  num_of_sem_filtered_clauses:            1
% 7.54/1.49  num_of_subtypes:                        2
% 7.54/1.49  monotx_restored_types:                  0
% 7.54/1.49  sat_num_of_epr_types:                   0
% 7.54/1.49  sat_num_of_non_cyclic_types:            0
% 7.54/1.49  sat_guarded_non_collapsed_types:        1
% 7.54/1.49  num_pure_diseq_elim:                    0
% 7.54/1.49  simp_replaced_by:                       0
% 7.54/1.49  res_preprocessed:                       150
% 7.54/1.49  prep_upred:                             0
% 7.54/1.49  prep_unflattend:                        104
% 7.54/1.49  smt_new_axioms:                         0
% 7.54/1.49  pred_elim_cands:                        6
% 7.54/1.49  pred_elim:                              5
% 7.54/1.49  pred_elim_cl:                           5
% 7.54/1.49  pred_elim_cycles:                       9
% 7.54/1.49  merged_defs:                            8
% 7.54/1.49  merged_defs_ncl:                        0
% 7.54/1.49  bin_hyper_res:                          8
% 7.54/1.49  prep_cycles:                            4
% 7.54/1.49  pred_elim_time:                         0.046
% 7.54/1.49  splitting_time:                         0.
% 7.54/1.49  sem_filter_time:                        0.
% 7.54/1.49  monotx_time:                            0.
% 7.54/1.49  subtype_inf_time:                       0.
% 7.54/1.49  
% 7.54/1.49  ------ Problem properties
% 7.54/1.49  
% 7.54/1.49  clauses:                                31
% 7.54/1.49  conjectures:                            8
% 7.54/1.49  epr:                                    2
% 7.54/1.49  horn:                                   23
% 7.54/1.49  ground:                                 5
% 7.54/1.49  unary:                                  5
% 7.54/1.49  binary:                                 4
% 7.54/1.49  lits:                                   99
% 7.54/1.49  lits_eq:                                8
% 7.54/1.49  fd_pure:                                0
% 7.54/1.49  fd_pseudo:                              0
% 7.54/1.49  fd_cond:                                0
% 7.54/1.49  fd_pseudo_cond:                         3
% 7.54/1.49  ac_symbols:                             0
% 7.54/1.49  
% 7.54/1.49  ------ Propositional Solver
% 7.54/1.49  
% 7.54/1.49  prop_solver_calls:                      31
% 7.54/1.49  prop_fast_solver_calls:                 2963
% 7.54/1.49  smt_solver_calls:                       0
% 7.54/1.49  smt_fast_solver_calls:                  0
% 7.54/1.49  prop_num_of_clauses:                    7655
% 7.54/1.49  prop_preprocess_simplified:             14154
% 7.54/1.49  prop_fo_subsumed:                       92
% 7.54/1.49  prop_solver_time:                       0.
% 7.54/1.49  smt_solver_time:                        0.
% 7.54/1.49  smt_fast_solver_time:                   0.
% 7.54/1.49  prop_fast_solver_time:                  0.
% 7.54/1.49  prop_unsat_core_time:                   0.
% 7.54/1.49  
% 7.54/1.49  ------ QBF
% 7.54/1.49  
% 7.54/1.49  qbf_q_res:                              0
% 7.54/1.49  qbf_num_tautologies:                    0
% 7.54/1.49  qbf_prep_cycles:                        0
% 7.54/1.49  
% 7.54/1.49  ------ BMC1
% 7.54/1.49  
% 7.54/1.49  bmc1_current_bound:                     -1
% 7.54/1.49  bmc1_last_solved_bound:                 -1
% 7.54/1.49  bmc1_unsat_core_size:                   -1
% 7.54/1.49  bmc1_unsat_core_parents_size:           -1
% 7.54/1.49  bmc1_merge_next_fun:                    0
% 7.54/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.54/1.49  
% 7.54/1.49  ------ Instantiation
% 7.54/1.49  
% 7.54/1.49  inst_num_of_clauses:                    1629
% 7.54/1.49  inst_num_in_passive:                    192
% 7.54/1.49  inst_num_in_active:                     997
% 7.54/1.49  inst_num_in_unprocessed:                440
% 7.54/1.49  inst_num_of_loops:                      1290
% 7.54/1.49  inst_num_of_learning_restarts:          0
% 7.54/1.49  inst_num_moves_active_passive:          288
% 7.54/1.49  inst_lit_activity:                      0
% 7.54/1.49  inst_lit_activity_moves:                0
% 7.54/1.49  inst_num_tautologies:                   0
% 7.54/1.49  inst_num_prop_implied:                  0
% 7.54/1.49  inst_num_existing_simplified:           0
% 7.54/1.49  inst_num_eq_res_simplified:             0
% 7.54/1.49  inst_num_child_elim:                    0
% 7.54/1.49  inst_num_of_dismatching_blockings:      625
% 7.54/1.49  inst_num_of_non_proper_insts:           1980
% 7.54/1.49  inst_num_of_duplicates:                 0
% 7.54/1.49  inst_inst_num_from_inst_to_res:         0
% 7.54/1.49  inst_dismatching_checking_time:         0.
% 7.54/1.49  
% 7.54/1.49  ------ Resolution
% 7.54/1.49  
% 7.54/1.49  res_num_of_clauses:                     0
% 7.54/1.49  res_num_in_passive:                     0
% 7.54/1.49  res_num_in_active:                      0
% 7.54/1.49  res_num_of_loops:                       154
% 7.54/1.49  res_forward_subset_subsumed:            57
% 7.54/1.49  res_backward_subset_subsumed:           0
% 7.54/1.49  res_forward_subsumed:                   0
% 7.54/1.49  res_backward_subsumed:                  0
% 7.54/1.49  res_forward_subsumption_resolution:     6
% 7.54/1.49  res_backward_subsumption_resolution:    0
% 7.54/1.49  res_clause_to_clause_subsumption:       1962
% 7.54/1.49  res_orphan_elimination:                 0
% 7.54/1.49  res_tautology_del:                      161
% 7.54/1.49  res_num_eq_res_simplified:              0
% 7.54/1.49  res_num_sel_changes:                    0
% 7.54/1.49  res_moves_from_active_to_pass:          0
% 7.54/1.49  
% 7.54/1.49  ------ Superposition
% 7.54/1.49  
% 7.54/1.49  sup_time_total:                         0.
% 7.54/1.49  sup_time_generating:                    0.
% 7.54/1.49  sup_time_sim_full:                      0.
% 7.54/1.49  sup_time_sim_immed:                     0.
% 7.54/1.49  
% 7.54/1.49  sup_num_of_clauses:                     471
% 7.54/1.49  sup_num_in_active:                      221
% 7.54/1.49  sup_num_in_passive:                     250
% 7.54/1.49  sup_num_of_loops:                       257
% 7.54/1.49  sup_fw_superposition:                   316
% 7.54/1.49  sup_bw_superposition:                   303
% 7.54/1.49  sup_immediate_simplified:               88
% 7.54/1.49  sup_given_eliminated:                   2
% 7.54/1.49  comparisons_done:                       0
% 7.54/1.49  comparisons_avoided:                    101
% 7.54/1.49  
% 7.54/1.49  ------ Simplifications
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  sim_fw_subset_subsumed:                 14
% 7.54/1.49  sim_bw_subset_subsumed:                 64
% 7.54/1.49  sim_fw_subsumed:                        25
% 7.54/1.49  sim_bw_subsumed:                        21
% 7.54/1.49  sim_fw_subsumption_res:                 0
% 7.54/1.49  sim_bw_subsumption_res:                 0
% 7.54/1.49  sim_tautology_del:                      12
% 7.54/1.49  sim_eq_tautology_del:                   11
% 7.54/1.49  sim_eq_res_simp:                        0
% 7.54/1.49  sim_fw_demodulated:                     25
% 7.54/1.49  sim_bw_demodulated:                     0
% 7.54/1.49  sim_light_normalised:                   18
% 7.54/1.49  sim_joinable_taut:                      0
% 7.54/1.49  sim_joinable_simp:                      0
% 7.54/1.49  sim_ac_normalised:                      0
% 7.54/1.49  sim_smt_subsumption:                    0
% 7.54/1.49  
%------------------------------------------------------------------------------
