%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:08 EST 2020

% Result     : Theorem 27.66s
% Output     : CNFRefutation 27.66s
% Verified   : 
% Statistics : Number of formulae       :  320 (5786 expanded)
%              Number of clauses        :  236 (1305 expanded)
%              Number of leaves         :   23 (1624 expanded)
%              Depth                    :   44
%              Number of atoms          : 1511 (95910 expanded)
%              Number of equality atoms :  525 (13381 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(nnf_transformation,[],[f21])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).

fof(f74,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
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

fof(f79,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
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

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(nnf_transformation,[],[f23])).

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

fof(f62,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_977,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_978,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_977])).

cnf(c_3790,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3813,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3820,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3810,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3817,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4123,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK6(X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_3817])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3902,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4146,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_3902])).

cnf(c_4147,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4146])).

cnf(c_4486,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK6(X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4123,c_42,c_4147])).

cnf(c_25,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3814,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_756,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_757,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_tarski(X2,X0) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_3802,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_4889,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_3802])).

cnf(c_4964,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_4889])).

cnf(c_3809,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3816,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4543,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3809,c_3816])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_941,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_942,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_3792,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_5198,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_3792])).

cnf(c_5258,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5198])).

cnf(c_6102,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4964,c_5258])).

cnf(c_11087,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_4889])).

cnf(c_22001,plain,
    ( r2_lattice3(sK2,sK6(X0),sK5) = iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_11087])).

cnf(c_20,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_790,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_791,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_3800,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_23,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_740,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_741,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_tarski(X2,X0) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_3803,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_5139,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k1_tarski(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3800,c_3803])).

cnf(c_6801,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5139])).

cnf(c_7835,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,sK5) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_6801])).

cnf(c_23430,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,sK6(X2),sK5) = iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22001,c_7835])).

cnf(c_30813,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,X2,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X3,sK4) != iProver_top
    | r1_tarski(X2,sK6(X3)) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23430,c_4889])).

cnf(c_61,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_63,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3009,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3036,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_962,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_963,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_3937,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_4030,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3937])).

cnf(c_4031,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4030])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_992,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_993,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_3979,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_4033,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3979])).

cnf(c_4034,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4033])).

cnf(c_3972,plain,
    ( r2_lattice3(sK2,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_4229,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_3972])).

cnf(c_4232,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4229])).

cnf(c_4477,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_4760,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_29,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4808,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4809,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4808])).

cnf(c_4807,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4811,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4807])).

cnf(c_6519,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3812,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4685,plain,
    ( k1_yellow_0(sK2,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_3812])).

cnf(c_4896,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
    | r2_lattice3(sK2,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_4685])).

cnf(c_6363,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_4896])).

cnf(c_6450,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6363,c_5258])).

cnf(c_7858,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6450,c_7835])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3808,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4544,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3808,c_3816])).

cnf(c_5257,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4544,c_5198])).

cnf(c_6039,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_5257])).

cnf(c_6054,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_orders_2(sK2,X1,sK5) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6039,c_4889])).

cnf(c_3789,plain,
    ( r2_lattice3(sK2,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_10502,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6054,c_3789])).

cnf(c_24782,plain,
    ( r2_lattice3(sK2,X1,sK5) = iProver_top
    | r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10502,c_61])).

cnf(c_24783,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,X1,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_24782])).

cnf(c_24788,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_24783])).

cnf(c_24793,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,X0,sK5) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24788,c_61])).

cnf(c_24794,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_24793])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_808,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_809,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_3799,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_24817,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24794,c_3799])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3885,plain,
    ( r2_hidden(X0,sK4)
    | ~ r1_tarski(k1_tarski(X0),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3886,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3885])).

cnf(c_25268,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24817,c_42,c_61,c_3886,c_4147])).

cnf(c_25274,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_25268])).

cnf(c_25603,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25274,c_7835])).

cnf(c_41224,plain,
    ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_41225,plain,
    ( m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41224])).

cnf(c_3012,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_40734,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_41046,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_40734])).

cnf(c_41171,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | X0 != sK0(sK2,sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_41046])).

cnf(c_41400,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4)
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_41171])).

cnf(c_41401,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | sK4 != sK4
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41400])).

cnf(c_41596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_43088,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_41596])).

cnf(c_43089,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43088])).

cnf(c_3010,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_41791,plain,
    ( X0 != X1
    | sK0(sK2,sK4,sK5) != X1
    | sK0(sK2,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_43415,plain,
    ( X0 != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = X0
    | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_41791])).

cnf(c_45515,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_43415])).

cnf(c_3015,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_41031,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | sK0(sK2,sK4,sK5) != X1
    | sK5 != X2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_41206,plain,
    ( ~ r1_orders_2(X0,X1,sK5)
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | sK0(sK2,sK4,sK5) != X1
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_41031])).

cnf(c_46366,plain,
    ( ~ r1_orders_2(X0,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_41206])).

cnf(c_46367,plain,
    ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != X0
    | r1_orders_2(X0,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46366])).

cnf(c_46369,plain,
    ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5
    | sK2 != sK2
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46367])).

cnf(c_16,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_857,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_858,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_41095,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_54796,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_41095])).

cnf(c_54797,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) = iProver_top
    | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54796])).

cnf(c_44268,plain,
    ( ~ r2_lattice3(sK2,X0,sK5)
    | r2_lattice3(sK2,sK6(sK0(X1,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(X1,sK4,sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_63330,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_44268])).

cnf(c_63331,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
    | r2_lattice3(sK2,sK3,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63330])).

cnf(c_67438,plain,
    ( r1_tarski(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_lattice3(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30813,c_42,c_61,c_63,c_3036,c_4031,c_4034,c_4232,c_4477,c_4760,c_4809,c_4811,c_6519,c_7858,c_25603,c_41225,c_41401,c_43089,c_45515,c_46369,c_54797,c_63331])).

cnf(c_67439,plain,
    ( r1_lattice3(sK2,X0,X1) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_67438])).

cnf(c_67444,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_67439])).

cnf(c_21,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_772,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_773,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_3801,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_67803,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_67444,c_3801])).

cnf(c_68213,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X0,X1) = iProver_top
    | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_67803,c_4543])).

cnf(c_68214,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_68213])).

cnf(c_68217,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK5,k1_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_68214])).

cnf(c_4009,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_tarski(k1_tarski(X0),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4010,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k1_tarski(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_3815,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25607,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_25274,c_3815])).

cnf(c_68243,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_orders_2(sK2,X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68217,c_42,c_61,c_3036,c_4010,c_4031,c_4034,c_4232,c_4477,c_4760,c_4809,c_4811,c_6450,c_6519,c_25268,c_25607,c_41225,c_41401,c_43089,c_45515,c_46369,c_54797,c_63331])).

cnf(c_68244,plain,
    ( r1_orders_2(sK2,X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_68243])).

cnf(c_68265,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_68244,c_3789])).

cnf(c_68497,plain,
    ( r2_lattice3(sK2,X0,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68265,c_61])).

cnf(c_68503,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_68497])).

cnf(c_68577,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68503,c_61])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_534,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_535,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_3806,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_5388,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_3806])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_507,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_5393,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5388,c_507])).

cnf(c_5399,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_5393])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_878,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_879,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_3795,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_899,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_900,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_3794,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_5574,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(X0),X1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_3799])).

cnf(c_14278,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
    | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
    | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_5574])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_920,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_921,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_3793,plain,
    ( k1_yellow_0(sK2,X0) = X1
    | r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,sK1(sK2,X0,X1)) != iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_47439,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r2_lattice3(sK2,k1_tarski(X0),X0) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14278,c_3793])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_513,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_36])).

cnf(c_514,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_518,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_37,c_35])).

cnf(c_18,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_824,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_825,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_1495,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X2
    | X1 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_518,c_825])).

cnf(c_1496,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1495])).

cnf(c_1497,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_47532,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47439,c_1497])).

cnf(c_47538,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5399,c_47532])).

cnf(c_49082,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47538,c_4544])).

cnf(c_49088,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0))) = sK0(sK2,sK3,X0)
    | r2_lattice3(sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_49082])).

cnf(c_49314,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_49088])).

cnf(c_49344,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_49314,c_3815])).

cnf(c_68581,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_68577,c_49344])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_550,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_3805,plain,
    ( k1_xboole_0 = k1_tarski(X0)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_4541,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_3816])).

cnf(c_5489,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | m1_subset_1(k1_yellow_0(sK2,k1_tarski(X0)),X1) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_4541])).

cnf(c_12555,plain,
    ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(X0)),X1) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5489,c_507])).

cnf(c_12576,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12555,c_5198])).

cnf(c_4124,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3809,c_3817])).

cnf(c_14022,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
    | r2_lattice3(sK2,X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12576,c_4124])).

cnf(c_14023,plain,
    ( r2_lattice3(sK2,X0,sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14022])).

cnf(c_14028,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X0)),sK5) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_14023])).

cnf(c_20646,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X0)),sK5) = iProver_top
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14028,c_507])).

cnf(c_68734,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68581,c_20646])).

cnf(c_3912,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5246,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_3912])).

cnf(c_5247,plain,
    ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5246])).

cnf(c_4105,plain,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(k1_tarski(X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4508,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_4105])).

cnf(c_4509,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4508])).

cnf(c_4082,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_3972])).

cnf(c_4083,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4082])).

cnf(c_4067,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3979])).

cnf(c_4071,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4067])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68734,c_68503,c_5247,c_4509,c_4083,c_4071,c_63,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 27.66/4.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.66/4.02  
% 27.66/4.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.66/4.02  
% 27.66/4.02  ------  iProver source info
% 27.66/4.02  
% 27.66/4.02  git: date: 2020-06-30 10:37:57 +0100
% 27.66/4.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.66/4.02  git: non_committed_changes: false
% 27.66/4.02  git: last_make_outside_of_git: false
% 27.66/4.02  
% 27.66/4.02  ------ 
% 27.66/4.02  
% 27.66/4.02  ------ Input Options
% 27.66/4.02  
% 27.66/4.02  --out_options                           all
% 27.66/4.02  --tptp_safe_out                         true
% 27.66/4.02  --problem_path                          ""
% 27.66/4.02  --include_path                          ""
% 27.66/4.02  --clausifier                            res/vclausify_rel
% 27.66/4.02  --clausifier_options                    ""
% 27.66/4.02  --stdin                                 false
% 27.66/4.02  --stats_out                             all
% 27.66/4.02  
% 27.66/4.02  ------ General Options
% 27.66/4.02  
% 27.66/4.02  --fof                                   false
% 27.66/4.02  --time_out_real                         305.
% 27.66/4.02  --time_out_virtual                      -1.
% 27.66/4.02  --symbol_type_check                     false
% 27.66/4.02  --clausify_out                          false
% 27.66/4.02  --sig_cnt_out                           false
% 27.66/4.02  --trig_cnt_out                          false
% 27.66/4.02  --trig_cnt_out_tolerance                1.
% 27.66/4.02  --trig_cnt_out_sk_spl                   false
% 27.66/4.02  --abstr_cl_out                          false
% 27.66/4.02  
% 27.66/4.02  ------ Global Options
% 27.66/4.02  
% 27.66/4.02  --schedule                              default
% 27.66/4.02  --add_important_lit                     false
% 27.66/4.02  --prop_solver_per_cl                    1000
% 27.66/4.02  --min_unsat_core                        false
% 27.66/4.02  --soft_assumptions                      false
% 27.66/4.02  --soft_lemma_size                       3
% 27.66/4.02  --prop_impl_unit_size                   0
% 27.66/4.02  --prop_impl_unit                        []
% 27.66/4.02  --share_sel_clauses                     true
% 27.66/4.02  --reset_solvers                         false
% 27.66/4.02  --bc_imp_inh                            [conj_cone]
% 27.66/4.02  --conj_cone_tolerance                   3.
% 27.66/4.02  --extra_neg_conj                        none
% 27.66/4.02  --large_theory_mode                     true
% 27.66/4.02  --prolific_symb_bound                   200
% 27.66/4.02  --lt_threshold                          2000
% 27.66/4.02  --clause_weak_htbl                      true
% 27.66/4.02  --gc_record_bc_elim                     false
% 27.66/4.02  
% 27.66/4.02  ------ Preprocessing Options
% 27.66/4.02  
% 27.66/4.02  --preprocessing_flag                    true
% 27.66/4.02  --time_out_prep_mult                    0.1
% 27.66/4.02  --splitting_mode                        input
% 27.66/4.02  --splitting_grd                         true
% 27.66/4.02  --splitting_cvd                         false
% 27.66/4.02  --splitting_cvd_svl                     false
% 27.66/4.02  --splitting_nvd                         32
% 27.66/4.02  --sub_typing                            true
% 27.66/4.02  --prep_gs_sim                           true
% 27.66/4.02  --prep_unflatten                        true
% 27.66/4.02  --prep_res_sim                          true
% 27.66/4.02  --prep_upred                            true
% 27.66/4.02  --prep_sem_filter                       exhaustive
% 27.66/4.02  --prep_sem_filter_out                   false
% 27.66/4.02  --pred_elim                             true
% 27.66/4.02  --res_sim_input                         true
% 27.66/4.02  --eq_ax_congr_red                       true
% 27.66/4.02  --pure_diseq_elim                       true
% 27.66/4.02  --brand_transform                       false
% 27.66/4.02  --non_eq_to_eq                          false
% 27.66/4.02  --prep_def_merge                        true
% 27.66/4.02  --prep_def_merge_prop_impl              false
% 27.66/4.02  --prep_def_merge_mbd                    true
% 27.66/4.02  --prep_def_merge_tr_red                 false
% 27.66/4.02  --prep_def_merge_tr_cl                  false
% 27.66/4.02  --smt_preprocessing                     true
% 27.66/4.02  --smt_ac_axioms                         fast
% 27.66/4.02  --preprocessed_out                      false
% 27.66/4.02  --preprocessed_stats                    false
% 27.66/4.02  
% 27.66/4.02  ------ Abstraction refinement Options
% 27.66/4.02  
% 27.66/4.02  --abstr_ref                             []
% 27.66/4.02  --abstr_ref_prep                        false
% 27.66/4.02  --abstr_ref_until_sat                   false
% 27.66/4.02  --abstr_ref_sig_restrict                funpre
% 27.66/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.66/4.02  --abstr_ref_under                       []
% 27.66/4.02  
% 27.66/4.02  ------ SAT Options
% 27.66/4.02  
% 27.66/4.02  --sat_mode                              false
% 27.66/4.02  --sat_fm_restart_options                ""
% 27.66/4.02  --sat_gr_def                            false
% 27.66/4.02  --sat_epr_types                         true
% 27.66/4.02  --sat_non_cyclic_types                  false
% 27.66/4.02  --sat_finite_models                     false
% 27.66/4.02  --sat_fm_lemmas                         false
% 27.66/4.02  --sat_fm_prep                           false
% 27.66/4.02  --sat_fm_uc_incr                        true
% 27.66/4.02  --sat_out_model                         small
% 27.66/4.02  --sat_out_clauses                       false
% 27.66/4.02  
% 27.66/4.02  ------ QBF Options
% 27.66/4.02  
% 27.66/4.02  --qbf_mode                              false
% 27.66/4.02  --qbf_elim_univ                         false
% 27.66/4.02  --qbf_dom_inst                          none
% 27.66/4.02  --qbf_dom_pre_inst                      false
% 27.66/4.02  --qbf_sk_in                             false
% 27.66/4.02  --qbf_pred_elim                         true
% 27.66/4.02  --qbf_split                             512
% 27.66/4.02  
% 27.66/4.02  ------ BMC1 Options
% 27.66/4.02  
% 27.66/4.02  --bmc1_incremental                      false
% 27.66/4.02  --bmc1_axioms                           reachable_all
% 27.66/4.02  --bmc1_min_bound                        0
% 27.66/4.02  --bmc1_max_bound                        -1
% 27.66/4.02  --bmc1_max_bound_default                -1
% 27.66/4.02  --bmc1_symbol_reachability              true
% 27.66/4.02  --bmc1_property_lemmas                  false
% 27.66/4.02  --bmc1_k_induction                      false
% 27.66/4.02  --bmc1_non_equiv_states                 false
% 27.66/4.02  --bmc1_deadlock                         false
% 27.66/4.02  --bmc1_ucm                              false
% 27.66/4.02  --bmc1_add_unsat_core                   none
% 27.66/4.02  --bmc1_unsat_core_children              false
% 27.66/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.66/4.02  --bmc1_out_stat                         full
% 27.66/4.02  --bmc1_ground_init                      false
% 27.66/4.02  --bmc1_pre_inst_next_state              false
% 27.66/4.02  --bmc1_pre_inst_state                   false
% 27.66/4.02  --bmc1_pre_inst_reach_state             false
% 27.66/4.02  --bmc1_out_unsat_core                   false
% 27.66/4.02  --bmc1_aig_witness_out                  false
% 27.66/4.02  --bmc1_verbose                          false
% 27.66/4.02  --bmc1_dump_clauses_tptp                false
% 27.66/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.66/4.02  --bmc1_dump_file                        -
% 27.66/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.66/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.66/4.02  --bmc1_ucm_extend_mode                  1
% 27.66/4.02  --bmc1_ucm_init_mode                    2
% 27.66/4.02  --bmc1_ucm_cone_mode                    none
% 27.66/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.66/4.02  --bmc1_ucm_relax_model                  4
% 27.66/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.66/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.66/4.02  --bmc1_ucm_layered_model                none
% 27.66/4.02  --bmc1_ucm_max_lemma_size               10
% 27.66/4.02  
% 27.66/4.02  ------ AIG Options
% 27.66/4.02  
% 27.66/4.02  --aig_mode                              false
% 27.66/4.02  
% 27.66/4.02  ------ Instantiation Options
% 27.66/4.02  
% 27.66/4.02  --instantiation_flag                    true
% 27.66/4.02  --inst_sos_flag                         true
% 27.66/4.02  --inst_sos_phase                        true
% 27.66/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.66/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.66/4.02  --inst_lit_sel_side                     num_symb
% 27.66/4.02  --inst_solver_per_active                1400
% 27.66/4.02  --inst_solver_calls_frac                1.
% 27.66/4.02  --inst_passive_queue_type               priority_queues
% 27.66/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.66/4.02  --inst_passive_queues_freq              [25;2]
% 27.66/4.02  --inst_dismatching                      true
% 27.66/4.02  --inst_eager_unprocessed_to_passive     true
% 27.66/4.02  --inst_prop_sim_given                   true
% 27.66/4.02  --inst_prop_sim_new                     false
% 27.66/4.02  --inst_subs_new                         false
% 27.66/4.02  --inst_eq_res_simp                      false
% 27.66/4.02  --inst_subs_given                       false
% 27.66/4.02  --inst_orphan_elimination               true
% 27.66/4.02  --inst_learning_loop_flag               true
% 27.66/4.02  --inst_learning_start                   3000
% 27.66/4.02  --inst_learning_factor                  2
% 27.66/4.02  --inst_start_prop_sim_after_learn       3
% 27.66/4.02  --inst_sel_renew                        solver
% 27.66/4.02  --inst_lit_activity_flag                true
% 27.66/4.02  --inst_restr_to_given                   false
% 27.66/4.02  --inst_activity_threshold               500
% 27.66/4.02  --inst_out_proof                        true
% 27.66/4.02  
% 27.66/4.02  ------ Resolution Options
% 27.66/4.02  
% 27.66/4.02  --resolution_flag                       true
% 27.66/4.02  --res_lit_sel                           adaptive
% 27.66/4.02  --res_lit_sel_side                      none
% 27.66/4.02  --res_ordering                          kbo
% 27.66/4.02  --res_to_prop_solver                    active
% 27.66/4.02  --res_prop_simpl_new                    false
% 27.66/4.02  --res_prop_simpl_given                  true
% 27.66/4.02  --res_passive_queue_type                priority_queues
% 27.66/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.66/4.02  --res_passive_queues_freq               [15;5]
% 27.66/4.02  --res_forward_subs                      full
% 27.66/4.02  --res_backward_subs                     full
% 27.66/4.02  --res_forward_subs_resolution           true
% 27.66/4.02  --res_backward_subs_resolution          true
% 27.66/4.02  --res_orphan_elimination                true
% 27.66/4.02  --res_time_limit                        2.
% 27.66/4.02  --res_out_proof                         true
% 27.66/4.02  
% 27.66/4.02  ------ Superposition Options
% 27.66/4.02  
% 27.66/4.02  --superposition_flag                    true
% 27.66/4.02  --sup_passive_queue_type                priority_queues
% 27.66/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.66/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.66/4.02  --demod_completeness_check              fast
% 27.66/4.02  --demod_use_ground                      true
% 27.66/4.02  --sup_to_prop_solver                    passive
% 27.66/4.02  --sup_prop_simpl_new                    true
% 27.66/4.02  --sup_prop_simpl_given                  true
% 27.66/4.02  --sup_fun_splitting                     true
% 27.66/4.02  --sup_smt_interval                      50000
% 27.66/4.02  
% 27.66/4.02  ------ Superposition Simplification Setup
% 27.66/4.02  
% 27.66/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.66/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.66/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.66/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.66/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.66/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.66/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.66/4.02  --sup_immed_triv                        [TrivRules]
% 27.66/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_immed_bw_main                     []
% 27.66/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.66/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.66/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_input_bw                          []
% 27.66/4.02  
% 27.66/4.02  ------ Combination Options
% 27.66/4.02  
% 27.66/4.02  --comb_res_mult                         3
% 27.66/4.02  --comb_sup_mult                         2
% 27.66/4.02  --comb_inst_mult                        10
% 27.66/4.02  
% 27.66/4.02  ------ Debug Options
% 27.66/4.02  
% 27.66/4.02  --dbg_backtrace                         false
% 27.66/4.02  --dbg_dump_prop_clauses                 false
% 27.66/4.02  --dbg_dump_prop_clauses_file            -
% 27.66/4.02  --dbg_out_stat                          false
% 27.66/4.02  ------ Parsing...
% 27.66/4.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.66/4.02  
% 27.66/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 27.66/4.02  
% 27.66/4.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.66/4.02  
% 27.66/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.66/4.02  ------ Proving...
% 27.66/4.02  ------ Problem Properties 
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  clauses                                 33
% 27.66/4.02  conjectures                             8
% 27.66/4.02  EPR                                     2
% 27.66/4.02  Horn                                    25
% 27.66/4.02  unary                                   4
% 27.66/4.02  binary                                  7
% 27.66/4.02  lits                                    101
% 27.66/4.02  lits eq                                 8
% 27.66/4.02  fd_pure                                 0
% 27.66/4.02  fd_pseudo                               0
% 27.66/4.02  fd_cond                                 0
% 27.66/4.02  fd_pseudo_cond                          3
% 27.66/4.02  AC symbols                              0
% 27.66/4.02  
% 27.66/4.02  ------ Schedule dynamic 5 is on 
% 27.66/4.02  
% 27.66/4.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  ------ 
% 27.66/4.02  Current options:
% 27.66/4.02  ------ 
% 27.66/4.02  
% 27.66/4.02  ------ Input Options
% 27.66/4.02  
% 27.66/4.02  --out_options                           all
% 27.66/4.02  --tptp_safe_out                         true
% 27.66/4.02  --problem_path                          ""
% 27.66/4.02  --include_path                          ""
% 27.66/4.02  --clausifier                            res/vclausify_rel
% 27.66/4.02  --clausifier_options                    ""
% 27.66/4.02  --stdin                                 false
% 27.66/4.02  --stats_out                             all
% 27.66/4.02  
% 27.66/4.02  ------ General Options
% 27.66/4.02  
% 27.66/4.02  --fof                                   false
% 27.66/4.02  --time_out_real                         305.
% 27.66/4.02  --time_out_virtual                      -1.
% 27.66/4.02  --symbol_type_check                     false
% 27.66/4.02  --clausify_out                          false
% 27.66/4.02  --sig_cnt_out                           false
% 27.66/4.02  --trig_cnt_out                          false
% 27.66/4.02  --trig_cnt_out_tolerance                1.
% 27.66/4.02  --trig_cnt_out_sk_spl                   false
% 27.66/4.02  --abstr_cl_out                          false
% 27.66/4.02  
% 27.66/4.02  ------ Global Options
% 27.66/4.02  
% 27.66/4.02  --schedule                              default
% 27.66/4.02  --add_important_lit                     false
% 27.66/4.02  --prop_solver_per_cl                    1000
% 27.66/4.02  --min_unsat_core                        false
% 27.66/4.02  --soft_assumptions                      false
% 27.66/4.02  --soft_lemma_size                       3
% 27.66/4.02  --prop_impl_unit_size                   0
% 27.66/4.02  --prop_impl_unit                        []
% 27.66/4.02  --share_sel_clauses                     true
% 27.66/4.02  --reset_solvers                         false
% 27.66/4.02  --bc_imp_inh                            [conj_cone]
% 27.66/4.02  --conj_cone_tolerance                   3.
% 27.66/4.02  --extra_neg_conj                        none
% 27.66/4.02  --large_theory_mode                     true
% 27.66/4.02  --prolific_symb_bound                   200
% 27.66/4.02  --lt_threshold                          2000
% 27.66/4.02  --clause_weak_htbl                      true
% 27.66/4.02  --gc_record_bc_elim                     false
% 27.66/4.02  
% 27.66/4.02  ------ Preprocessing Options
% 27.66/4.02  
% 27.66/4.02  --preprocessing_flag                    true
% 27.66/4.02  --time_out_prep_mult                    0.1
% 27.66/4.02  --splitting_mode                        input
% 27.66/4.02  --splitting_grd                         true
% 27.66/4.02  --splitting_cvd                         false
% 27.66/4.02  --splitting_cvd_svl                     false
% 27.66/4.02  --splitting_nvd                         32
% 27.66/4.02  --sub_typing                            true
% 27.66/4.02  --prep_gs_sim                           true
% 27.66/4.02  --prep_unflatten                        true
% 27.66/4.02  --prep_res_sim                          true
% 27.66/4.02  --prep_upred                            true
% 27.66/4.02  --prep_sem_filter                       exhaustive
% 27.66/4.02  --prep_sem_filter_out                   false
% 27.66/4.02  --pred_elim                             true
% 27.66/4.02  --res_sim_input                         true
% 27.66/4.02  --eq_ax_congr_red                       true
% 27.66/4.02  --pure_diseq_elim                       true
% 27.66/4.02  --brand_transform                       false
% 27.66/4.02  --non_eq_to_eq                          false
% 27.66/4.02  --prep_def_merge                        true
% 27.66/4.02  --prep_def_merge_prop_impl              false
% 27.66/4.02  --prep_def_merge_mbd                    true
% 27.66/4.02  --prep_def_merge_tr_red                 false
% 27.66/4.02  --prep_def_merge_tr_cl                  false
% 27.66/4.02  --smt_preprocessing                     true
% 27.66/4.02  --smt_ac_axioms                         fast
% 27.66/4.02  --preprocessed_out                      false
% 27.66/4.02  --preprocessed_stats                    false
% 27.66/4.02  
% 27.66/4.02  ------ Abstraction refinement Options
% 27.66/4.02  
% 27.66/4.02  --abstr_ref                             []
% 27.66/4.02  --abstr_ref_prep                        false
% 27.66/4.02  --abstr_ref_until_sat                   false
% 27.66/4.02  --abstr_ref_sig_restrict                funpre
% 27.66/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.66/4.02  --abstr_ref_under                       []
% 27.66/4.02  
% 27.66/4.02  ------ SAT Options
% 27.66/4.02  
% 27.66/4.02  --sat_mode                              false
% 27.66/4.02  --sat_fm_restart_options                ""
% 27.66/4.02  --sat_gr_def                            false
% 27.66/4.02  --sat_epr_types                         true
% 27.66/4.02  --sat_non_cyclic_types                  false
% 27.66/4.02  --sat_finite_models                     false
% 27.66/4.02  --sat_fm_lemmas                         false
% 27.66/4.02  --sat_fm_prep                           false
% 27.66/4.02  --sat_fm_uc_incr                        true
% 27.66/4.02  --sat_out_model                         small
% 27.66/4.02  --sat_out_clauses                       false
% 27.66/4.02  
% 27.66/4.02  ------ QBF Options
% 27.66/4.02  
% 27.66/4.02  --qbf_mode                              false
% 27.66/4.02  --qbf_elim_univ                         false
% 27.66/4.02  --qbf_dom_inst                          none
% 27.66/4.02  --qbf_dom_pre_inst                      false
% 27.66/4.02  --qbf_sk_in                             false
% 27.66/4.02  --qbf_pred_elim                         true
% 27.66/4.02  --qbf_split                             512
% 27.66/4.02  
% 27.66/4.02  ------ BMC1 Options
% 27.66/4.02  
% 27.66/4.02  --bmc1_incremental                      false
% 27.66/4.02  --bmc1_axioms                           reachable_all
% 27.66/4.02  --bmc1_min_bound                        0
% 27.66/4.02  --bmc1_max_bound                        -1
% 27.66/4.02  --bmc1_max_bound_default                -1
% 27.66/4.02  --bmc1_symbol_reachability              true
% 27.66/4.02  --bmc1_property_lemmas                  false
% 27.66/4.02  --bmc1_k_induction                      false
% 27.66/4.02  --bmc1_non_equiv_states                 false
% 27.66/4.02  --bmc1_deadlock                         false
% 27.66/4.02  --bmc1_ucm                              false
% 27.66/4.02  --bmc1_add_unsat_core                   none
% 27.66/4.02  --bmc1_unsat_core_children              false
% 27.66/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.66/4.02  --bmc1_out_stat                         full
% 27.66/4.02  --bmc1_ground_init                      false
% 27.66/4.02  --bmc1_pre_inst_next_state              false
% 27.66/4.02  --bmc1_pre_inst_state                   false
% 27.66/4.02  --bmc1_pre_inst_reach_state             false
% 27.66/4.02  --bmc1_out_unsat_core                   false
% 27.66/4.02  --bmc1_aig_witness_out                  false
% 27.66/4.02  --bmc1_verbose                          false
% 27.66/4.02  --bmc1_dump_clauses_tptp                false
% 27.66/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.66/4.02  --bmc1_dump_file                        -
% 27.66/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.66/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.66/4.02  --bmc1_ucm_extend_mode                  1
% 27.66/4.02  --bmc1_ucm_init_mode                    2
% 27.66/4.02  --bmc1_ucm_cone_mode                    none
% 27.66/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.66/4.02  --bmc1_ucm_relax_model                  4
% 27.66/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.66/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.66/4.02  --bmc1_ucm_layered_model                none
% 27.66/4.02  --bmc1_ucm_max_lemma_size               10
% 27.66/4.02  
% 27.66/4.02  ------ AIG Options
% 27.66/4.02  
% 27.66/4.02  --aig_mode                              false
% 27.66/4.02  
% 27.66/4.02  ------ Instantiation Options
% 27.66/4.02  
% 27.66/4.02  --instantiation_flag                    true
% 27.66/4.02  --inst_sos_flag                         true
% 27.66/4.02  --inst_sos_phase                        true
% 27.66/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.66/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.66/4.02  --inst_lit_sel_side                     none
% 27.66/4.02  --inst_solver_per_active                1400
% 27.66/4.02  --inst_solver_calls_frac                1.
% 27.66/4.02  --inst_passive_queue_type               priority_queues
% 27.66/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.66/4.02  --inst_passive_queues_freq              [25;2]
% 27.66/4.02  --inst_dismatching                      true
% 27.66/4.02  --inst_eager_unprocessed_to_passive     true
% 27.66/4.02  --inst_prop_sim_given                   true
% 27.66/4.02  --inst_prop_sim_new                     false
% 27.66/4.02  --inst_subs_new                         false
% 27.66/4.02  --inst_eq_res_simp                      false
% 27.66/4.02  --inst_subs_given                       false
% 27.66/4.02  --inst_orphan_elimination               true
% 27.66/4.02  --inst_learning_loop_flag               true
% 27.66/4.02  --inst_learning_start                   3000
% 27.66/4.02  --inst_learning_factor                  2
% 27.66/4.02  --inst_start_prop_sim_after_learn       3
% 27.66/4.02  --inst_sel_renew                        solver
% 27.66/4.02  --inst_lit_activity_flag                true
% 27.66/4.02  --inst_restr_to_given                   false
% 27.66/4.02  --inst_activity_threshold               500
% 27.66/4.02  --inst_out_proof                        true
% 27.66/4.02  
% 27.66/4.02  ------ Resolution Options
% 27.66/4.02  
% 27.66/4.02  --resolution_flag                       false
% 27.66/4.02  --res_lit_sel                           adaptive
% 27.66/4.02  --res_lit_sel_side                      none
% 27.66/4.02  --res_ordering                          kbo
% 27.66/4.02  --res_to_prop_solver                    active
% 27.66/4.02  --res_prop_simpl_new                    false
% 27.66/4.02  --res_prop_simpl_given                  true
% 27.66/4.02  --res_passive_queue_type                priority_queues
% 27.66/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.66/4.02  --res_passive_queues_freq               [15;5]
% 27.66/4.02  --res_forward_subs                      full
% 27.66/4.02  --res_backward_subs                     full
% 27.66/4.02  --res_forward_subs_resolution           true
% 27.66/4.02  --res_backward_subs_resolution          true
% 27.66/4.02  --res_orphan_elimination                true
% 27.66/4.02  --res_time_limit                        2.
% 27.66/4.02  --res_out_proof                         true
% 27.66/4.02  
% 27.66/4.02  ------ Superposition Options
% 27.66/4.02  
% 27.66/4.02  --superposition_flag                    true
% 27.66/4.02  --sup_passive_queue_type                priority_queues
% 27.66/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.66/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.66/4.02  --demod_completeness_check              fast
% 27.66/4.02  --demod_use_ground                      true
% 27.66/4.02  --sup_to_prop_solver                    passive
% 27.66/4.02  --sup_prop_simpl_new                    true
% 27.66/4.02  --sup_prop_simpl_given                  true
% 27.66/4.02  --sup_fun_splitting                     true
% 27.66/4.02  --sup_smt_interval                      50000
% 27.66/4.02  
% 27.66/4.02  ------ Superposition Simplification Setup
% 27.66/4.02  
% 27.66/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.66/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.66/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.66/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.66/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.66/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.66/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.66/4.02  --sup_immed_triv                        [TrivRules]
% 27.66/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_immed_bw_main                     []
% 27.66/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.66/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.66/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.66/4.02  --sup_input_bw                          []
% 27.66/4.02  
% 27.66/4.02  ------ Combination Options
% 27.66/4.02  
% 27.66/4.02  --comb_res_mult                         3
% 27.66/4.02  --comb_sup_mult                         2
% 27.66/4.02  --comb_inst_mult                        10
% 27.66/4.02  
% 27.66/4.02  ------ Debug Options
% 27.66/4.02  
% 27.66/4.02  --dbg_backtrace                         false
% 27.66/4.02  --dbg_dump_prop_clauses                 false
% 27.66/4.02  --dbg_dump_prop_clauses_file            -
% 27.66/4.02  --dbg_out_stat                          false
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  ------ Proving...
% 27.66/4.02  
% 27.66/4.02  
% 27.66/4.02  % SZS status Theorem for theBenchmark.p
% 27.66/4.02  
% 27.66/4.02  % SZS output start CNFRefutation for theBenchmark.p
% 27.66/4.02  
% 27.66/4.02  fof(f8,axiom,(
% 27.66/4.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f20,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(ennf_transformation,[],[f8])).
% 27.66/4.02  
% 27.66/4.02  fof(f21,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(flattening,[],[f20])).
% 27.66/4.02  
% 27.66/4.02  fof(f30,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(nnf_transformation,[],[f21])).
% 27.66/4.02  
% 27.66/4.02  fof(f31,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(rectify,[],[f30])).
% 27.66/4.02  
% 27.66/4.02  fof(f32,plain,(
% 27.66/4.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f33,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 27.66/4.02  
% 27.66/4.02  fof(f59,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f33])).
% 27.66/4.02  
% 27.66/4.02  fof(f12,conjecture,(
% 27.66/4.02    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f13,negated_conjecture,(
% 27.66/4.02    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 27.66/4.02    inference(negated_conjecture,[],[f12])).
% 27.66/4.02  
% 27.66/4.02  fof(f14,plain,(
% 27.66/4.02    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 27.66/4.02    inference(rectify,[],[f13])).
% 27.66/4.02  
% 27.66/4.02  fof(f15,plain,(
% 27.66/4.02    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 27.66/4.02    inference(pure_predicate_removal,[],[f14])).
% 27.66/4.02  
% 27.66/4.02  fof(f26,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 27.66/4.02    inference(ennf_transformation,[],[f15])).
% 27.66/4.02  
% 27.66/4.02  fof(f27,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.66/4.02    inference(flattening,[],[f26])).
% 27.66/4.02  
% 27.66/4.02  fof(f39,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.66/4.02    inference(nnf_transformation,[],[f27])).
% 27.66/4.02  
% 27.66/4.02  fof(f40,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.66/4.02    inference(flattening,[],[f39])).
% 27.66/4.02  
% 27.66/4.02  fof(f41,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 27.66/4.02    inference(rectify,[],[f40])).
% 27.66/4.02  
% 27.66/4.02  fof(f46,plain,(
% 27.66/4.02    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f45,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f44,plain,(
% 27.66/4.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f43,plain,(
% 27.66/4.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f42,plain,(
% 27.66/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f47,plain,(
% 27.66/4.02    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 27.66/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f41,f46,f45,f44,f43,f42])).
% 27.66/4.02  
% 27.66/4.02  fof(f74,plain,(
% 27.66/4.02    l1_orders_2(sK2)),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f83,plain,(
% 27.66/4.02    m1_subset_1(sK5,u1_struct_0(sK2))),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f3,axiom,(
% 27.66/4.02    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f28,plain,(
% 27.66/4.02    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 27.66/4.02    inference(nnf_transformation,[],[f3])).
% 27.66/4.02  
% 27.66/4.02  fof(f51,plain,(
% 27.66/4.02    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f28])).
% 27.66/4.02  
% 27.66/4.02  fof(f79,plain,(
% 27.66/4.02    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f4,axiom,(
% 27.66/4.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f29,plain,(
% 27.66/4.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.66/4.02    inference(nnf_transformation,[],[f4])).
% 27.66/4.02  
% 27.66/4.02  fof(f52,plain,(
% 27.66/4.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f29])).
% 27.66/4.02  
% 27.66/4.02  fof(f76,plain,(
% 27.66/4.02    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f5,axiom,(
% 27.66/4.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f16,plain,(
% 27.66/4.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 27.66/4.02    inference(ennf_transformation,[],[f5])).
% 27.66/4.02  
% 27.66/4.02  fof(f17,plain,(
% 27.66/4.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.66/4.02    inference(flattening,[],[f16])).
% 27.66/4.02  
% 27.66/4.02  fof(f54,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f17])).
% 27.66/4.02  
% 27.66/4.02  fof(f84,plain,(
% 27.66/4.02    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f11,axiom,(
% 27.66/4.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f25,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(ennf_transformation,[],[f11])).
% 27.66/4.02  
% 27.66/4.02  fof(f71,plain,(
% 27.66/4.02    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f25])).
% 27.66/4.02  
% 27.66/4.02  fof(f57,plain,(
% 27.66/4.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f33])).
% 27.66/4.02  
% 27.66/4.02  fof(f10,axiom,(
% 27.66/4.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f24,plain,(
% 27.66/4.02    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(ennf_transformation,[],[f10])).
% 27.66/4.02  
% 27.66/4.02  fof(f67,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f24])).
% 27.66/4.02  
% 27.66/4.02  fof(f70,plain,(
% 27.66/4.02    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f25])).
% 27.66/4.02  
% 27.66/4.02  fof(f85,plain,(
% 27.66/4.02    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f58,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f33])).
% 27.66/4.02  
% 27.66/4.02  fof(f60,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f33])).
% 27.66/4.02  
% 27.66/4.02  fof(f80,plain,(
% 27.66/4.02    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f81,plain,(
% 27.66/4.02    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f75,plain,(
% 27.66/4.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f68,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f24])).
% 27.66/4.02  
% 27.66/4.02  fof(f50,plain,(
% 27.66/4.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f28])).
% 27.66/4.02  
% 27.66/4.02  fof(f9,axiom,(
% 27.66/4.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f22,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(ennf_transformation,[],[f9])).
% 27.66/4.02  
% 27.66/4.02  fof(f23,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(flattening,[],[f22])).
% 27.66/4.02  
% 27.66/4.02  fof(f34,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(nnf_transformation,[],[f23])).
% 27.66/4.02  
% 27.66/4.02  fof(f35,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(flattening,[],[f34])).
% 27.66/4.02  
% 27.66/4.02  fof(f36,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(rectify,[],[f35])).
% 27.66/4.02  
% 27.66/4.02  fof(f37,plain,(
% 27.66/4.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 27.66/4.02    introduced(choice_axiom,[])).
% 27.66/4.02  
% 27.66/4.02  fof(f38,plain,(
% 27.66/4.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 27.66/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 27.66/4.02  
% 27.66/4.02  fof(f62,plain,(
% 27.66/4.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f38])).
% 27.66/4.02  
% 27.66/4.02  fof(f86,plain,(
% 27.66/4.02    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(equality_resolution,[],[f62])).
% 27.66/4.02  
% 27.66/4.02  fof(f66,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f24])).
% 27.66/4.02  
% 27.66/4.02  fof(f53,plain,(
% 27.66/4.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f29])).
% 27.66/4.02  
% 27.66/4.02  fof(f6,axiom,(
% 27.66/4.02    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f55,plain,(
% 27.66/4.02    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f6])).
% 27.66/4.02  
% 27.66/4.02  fof(f77,plain,(
% 27.66/4.02    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f1,axiom,(
% 27.66/4.02    v1_xboole_0(k1_xboole_0)),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f48,plain,(
% 27.66/4.02    v1_xboole_0(k1_xboole_0)),
% 27.66/4.02    inference(cnf_transformation,[],[f1])).
% 27.66/4.02  
% 27.66/4.02  fof(f2,axiom,(
% 27.66/4.02    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f49,plain,(
% 27.66/4.02    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 27.66/4.02    inference(cnf_transformation,[],[f2])).
% 27.66/4.02  
% 27.66/4.02  fof(f63,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f38])).
% 27.66/4.02  
% 27.66/4.02  fof(f64,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f38])).
% 27.66/4.02  
% 27.66/4.02  fof(f65,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f38])).
% 27.66/4.02  
% 27.66/4.02  fof(f7,axiom,(
% 27.66/4.02    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 27.66/4.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.66/4.02  
% 27.66/4.02  fof(f18,plain,(
% 27.66/4.02    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 27.66/4.02    inference(ennf_transformation,[],[f7])).
% 27.66/4.02  
% 27.66/4.02  fof(f19,plain,(
% 27.66/4.02    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 27.66/4.02    inference(flattening,[],[f18])).
% 27.66/4.02  
% 27.66/4.02  fof(f56,plain,(
% 27.66/4.02    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f19])).
% 27.66/4.02  
% 27.66/4.02  fof(f73,plain,(
% 27.66/4.02    v3_orders_2(sK2)),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f72,plain,(
% 27.66/4.02    ~v2_struct_0(sK2)),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  fof(f69,plain,(
% 27.66/4.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f24])).
% 27.66/4.02  
% 27.66/4.02  fof(f82,plain,(
% 27.66/4.02    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 27.66/4.02    inference(cnf_transformation,[],[f47])).
% 27.66/4.02  
% 27.66/4.02  cnf(c_10,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | r2_hidden(sK0(X0,X1,X2),X1)
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f59]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_35,negated_conjecture,
% 27.66/4.02      ( l1_orders_2(sK2) ),
% 27.66/4.02      inference(cnf_transformation,[],[f74]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_977,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | r2_hidden(sK0(X0,X1,X2),X1)
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_978,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.02      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_977]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3790,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,X0,X1),X0) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_26,negated_conjecture,
% 27.66/4.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(cnf_transformation,[],[f83]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3813,plain,
% 27.66/4.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_2,plain,
% 27.66/4.02      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 27.66/4.02      inference(cnf_transformation,[],[f51]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3820,plain,
% 27.66/4.02      ( r2_hidden(X0,X1) != iProver_top
% 27.66/4.02      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_30,negated_conjecture,
% 27.66/4.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3))
% 27.66/4.02      | ~ r2_hidden(X0,sK4) ),
% 27.66/4.02      inference(cnf_transformation,[],[f79]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3810,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_5,plain,
% 27.66/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.66/4.02      inference(cnf_transformation,[],[f52]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3817,plain,
% 27.66/4.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/4.02      | r1_tarski(X0,X1) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4123,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(sK6(X0),sK3) = iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3810,c_3817]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_33,negated_conjecture,
% 27.66/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 27.66/4.02      inference(cnf_transformation,[],[f76]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_42,plain,
% 27.66/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6,plain,
% 27.66/4.02      ( m1_subset_1(X0,X1)
% 27.66/4.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.66/4.02      | ~ r2_hidden(X0,X2) ),
% 27.66/4.02      inference(cnf_transformation,[],[f54]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3902,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 27.66/4.02      | ~ r2_hidden(X0,X1) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_6]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4146,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 27.66/4.02      | ~ r2_hidden(X0,sK4) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3902]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4147,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 27.66/4.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4146]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4486,plain,
% 27.66/4.02      ( r2_hidden(X0,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(sK6(X0),sK3) = iProver_top ),
% 27.66/4.02      inference(global_propositional_subsumption,
% 27.66/4.02                [status(thm)],
% 27.66/4.02                [c_4123,c_42,c_4147]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_25,negated_conjecture,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 27.66/4.02      inference(cnf_transformation,[],[f84]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3814,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_22,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.02      | r2_lattice3(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ r1_tarski(X3,X1)
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f71]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_756,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.02      | r2_lattice3(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ r1_tarski(X3,X1)
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_757,plain,
% 27.66/4.02      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.02      | r2_lattice3(sK2,X2,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.02      | ~ r1_tarski(X2,X0) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_756]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3802,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X2,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r1_tarski(X2,X0) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4889,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r1_tarski(X1,X0) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3813,c_3802]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4964,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.02      | r1_tarski(X0,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3814,c_4889]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3809,plain,
% 27.66/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3816,plain,
% 27.66/4.02      ( m1_subset_1(X0,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 27.66/4.02      | r2_hidden(X0,X2) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4543,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3809,c_3816]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_12,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.02      | r1_orders_2(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.66/4.02      | ~ r2_hidden(X3,X1)
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f57]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_941,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.02      | r1_orders_2(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.66/4.02      | ~ r2_hidden(X3,X1)
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_942,plain,
% 27.66/4.02      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.02      | r1_orders_2(sK2,X2,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 27.66/4.02      | ~ r2_hidden(X2,X0) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_941]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3792,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X2,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(X2,X0) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_5198,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(X1,X0) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3813,c_3792]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_5258,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,X0) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4543,c_5198]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6102,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4964,c_5258]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_11087,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,X2) != iProver_top
% 27.66/4.02      | r1_tarski(X2,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_6102,c_4889]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_22001,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK6(X0),sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(sK3,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4486,c_11087]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_20,plain,
% 27.66/4.02      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.02      | ~ r1_orders_2(X0,X2,X1)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f67]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_790,plain,
% 27.66/4.02      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.02      | ~ r1_orders_2(X0,X2,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_791,plain,
% 27.66/4.02      ( r1_lattice3(sK2,k1_tarski(X0),X1)
% 27.66/4.02      | ~ r1_orders_2(sK2,X1,X0)
% 27.66/4.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_790]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3800,plain,
% 27.66/4.02      ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,X0) != iProver_top
% 27.66/4.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_23,plain,
% 27.66/4.02      ( ~ r1_lattice3(X0,X1,X2)
% 27.66/4.02      | r1_lattice3(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ r1_tarski(X3,X1)
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f70]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_740,plain,
% 27.66/4.02      ( ~ r1_lattice3(X0,X1,X2)
% 27.66/4.02      | r1_lattice3(X0,X3,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ r1_tarski(X3,X1)
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_741,plain,
% 27.66/4.02      ( ~ r1_lattice3(sK2,X0,X1)
% 27.66/4.02      | r1_lattice3(sK2,X2,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.02      | ~ r1_tarski(X2,X0) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_740]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3803,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.02      | r1_lattice3(sK2,X2,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r1_tarski(X2,X0) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_5139,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,X2) != iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(X2)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3800,c_3803]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6801,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,X2) != iProver_top
% 27.66/4.02      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(X2)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4543,c_5139]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_7835,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3813,c_6801]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_23430,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK6(X2),sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X2,sK4) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top
% 27.66/4.02      | r1_tarski(sK3,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_22001,c_7835]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_30813,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X2,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r2_hidden(X3,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X2,sK6(X3)) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top
% 27.66/4.02      | r1_tarski(sK3,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_23430,c_4889]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_61,plain,
% 27.66/4.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24,negated_conjecture,
% 27.66/4.02      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 27.66/4.02      inference(cnf_transformation,[],[f85]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_63,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3009,plain,( X0 = X0 ),theory(equality) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3036,plain,
% 27.66/4.02      ( sK2 = sK2 ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3009]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_11,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f58]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_962,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_963,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.02      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_962]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3937,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5)
% 27.66/4.02      | m1_subset_1(sK0(sK2,X0,sK5),u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_963]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4030,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5)
% 27.66/4.02      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3937]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4031,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4030]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_9,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f60]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_992,plain,
% 27.66/4.02      ( r2_lattice3(X0,X1,X2)
% 27.66/4.02      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_993,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1)
% 27.66/4.02      | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_992]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3979,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5)
% 27.66/4.02      | ~ r1_orders_2(sK2,sK0(sK2,X0,sK5),sK5)
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_993]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4033,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5)
% 27.66/4.02      | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3979]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4034,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) != iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4033]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3972,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5)
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.66/4.02      | r2_hidden(sK0(sK2,X0,sK5),X0) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_978]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4229,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5)
% 27.66/4.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.66/4.02      | r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3972]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4232,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4229]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4477,plain,
% 27.66/4.02      ( sK4 = sK4 ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3009]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4760,plain,
% 27.66/4.02      ( sK5 = sK5 ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3009]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_29,negated_conjecture,
% 27.66/4.02      ( r1_yellow_0(sK2,sK6(X0))
% 27.66/4.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ r2_hidden(X0,sK4) ),
% 27.66/4.02      inference(cnf_transformation,[],[f80]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4808,plain,
% 27.66/4.02      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.02      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 27.66/4.02      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_29]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4809,plain,
% 27.66/4.02      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = iProver_top
% 27.66/4.02      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4808]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4807,plain,
% 27.66/4.02      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 27.66/4.02      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 27.66/4.02      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_30]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4811,plain,
% 27.66/4.02      ( m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_4807]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6519,plain,
% 27.66/4.02      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3009]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_28,negated_conjecture,
% 27.66/4.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ r2_hidden(X0,sK4)
% 27.66/4.02      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 27.66/4.02      inference(cnf_transformation,[],[f81]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3812,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(X0)) = X0
% 27.66/4.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4685,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(X0)) = X0
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4543,c_3812]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4896,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0))) = sK0(sK2,sK4,X0)
% 27.66/4.02      | r2_lattice3(sK2,sK4,X0) = iProver_top
% 27.66/4.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3790,c_4685]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6363,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 27.66/4.02      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3813,c_4896]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6450,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 27.66/4.02      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_6363,c_5258]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_7858,plain,
% 27.66/4.02      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 27.66/4.02      | r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_6450,c_7835]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_34,negated_conjecture,
% 27.66/4.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 27.66/4.02      inference(cnf_transformation,[],[f75]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3808,plain,
% 27.66/4.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_4544,plain,
% 27.66/4.02      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3808,c_3816]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_5257,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,X0) != iProver_top
% 27.66/4.02      | r2_hidden(X1,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_4544,c_5198]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6039,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK3) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3814,c_5257]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_6054,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK3) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_6039,c_4889]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3789,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,sK0(sK2,X0,X1),X1) != iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_993]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_10502,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_6054,c_3789]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24782,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(global_propositional_subsumption,
% 27.66/4.02                [status(thm)],
% 27.66/4.02                [c_10502,c_61]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24783,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X1,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(sK0(sK2,X1,sK5),sK3) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(renaming,[status(thm)],[c_24782]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24788,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3790,c_24783]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24793,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(global_propositional_subsumption,
% 27.66/4.02                [status(thm)],
% 27.66/4.02                [c_24788,c_61]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24794,plain,
% 27.66/4.02      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r1_tarski(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(renaming,[status(thm)],[c_24793]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_19,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.02      | r1_orders_2(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.02      | ~ l1_orders_2(X0) ),
% 27.66/4.02      inference(cnf_transformation,[],[f68]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_808,plain,
% 27.66/4.02      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.02      | r1_orders_2(X0,X1,X2)
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.02      | sK2 != X0 ),
% 27.66/4.02      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_809,plain,
% 27.66/4.02      ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 27.66/4.02      | r1_orders_2(sK2,X0,X1)
% 27.66/4.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 27.66/4.02      inference(unflattening,[status(thm)],[c_808]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3799,plain,
% 27.66/4.02      ( r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X0,X1) = iProver_top
% 27.66/4.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_24817,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.02      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_24794,c_3799]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3,plain,
% 27.66/4.02      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 27.66/4.02      inference(cnf_transformation,[],[f50]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3885,plain,
% 27.66/4.02      ( r2_hidden(X0,sK4) | ~ r1_tarski(k1_tarski(X0),sK4) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_3]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3886,plain,
% 27.66/4.02      ( r2_hidden(X0,sK4) = iProver_top
% 27.66/4.02      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_3885]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_25268,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r1_tarski(k1_tarski(X0),sK4) != iProver_top ),
% 27.66/4.02      inference(global_propositional_subsumption,
% 27.66/4.02                [status(thm)],
% 27.66/4.02                [c_24817,c_42,c_61,c_3886,c_4147]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_25274,plain,
% 27.66/4.02      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_3820,c_25268]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_25603,plain,
% 27.66/4.02      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.02      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.02      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.02      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
% 27.66/4.02      inference(superposition,[status(thm)],[c_25274,c_7835]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_41224,plain,
% 27.66/4.02      ( ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 27.66/4.02      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 27.66/4.02      inference(instantiation,[status(thm)],[c_5]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_41225,plain,
% 27.66/4.02      ( m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.02      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) = iProver_top ),
% 27.66/4.02      inference(predicate_to_equality,[status(thm)],[c_41224]) ).
% 27.66/4.02  
% 27.66/4.02  cnf(c_3012,plain,
% 27.66/4.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.66/4.03      theory(equality) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_40734,plain,
% 27.66/4.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK4) | X2 != X0 | sK4 != X1 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3012]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41046,plain,
% 27.66/4.03      ( ~ r2_hidden(X0,sK4) | r2_hidden(X1,sK4) | X1 != X0 | sK4 != sK4 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_40734]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41171,plain,
% 27.66/4.03      ( r2_hidden(X0,sK4)
% 27.66/4.03      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 27.66/4.03      | X0 != sK0(sK2,sK4,sK5)
% 27.66/4.03      | sK4 != sK4 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41046]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41400,plain,
% 27.66/4.03      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4)
% 27.66/4.03      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 27.66/4.03      | sK4 != sK4 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41171]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41401,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 27.66/4.03      | sK4 != sK4
% 27.66/4.03      | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_41400]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41596,plain,
% 27.66/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 27.66/4.03      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 27.66/4.03      | ~ r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_6]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_43088,plain,
% 27.66/4.03      ( m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 27.66/4.03      | ~ r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41596]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_43089,plain,
% 27.66/4.03      ( m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) = iProver_top
% 27.66/4.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK4) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_43088]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3010,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41791,plain,
% 27.66/4.03      ( X0 != X1 | sK0(sK2,sK4,sK5) != X1 | sK0(sK2,sK4,sK5) = X0 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3010]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_43415,plain,
% 27.66/4.03      ( X0 != sK0(sK2,sK4,sK5)
% 27.66/4.03      | sK0(sK2,sK4,sK5) = X0
% 27.66/4.03      | sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41791]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_45515,plain,
% 27.66/4.03      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 27.66/4.03      | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_43415]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3015,plain,
% 27.66/4.03      ( ~ r1_orders_2(X0,X1,X2)
% 27.66/4.03      | r1_orders_2(X3,X4,X5)
% 27.66/4.03      | X3 != X0
% 27.66/4.03      | X4 != X1
% 27.66/4.03      | X5 != X2 ),
% 27.66/4.03      theory(equality) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41031,plain,
% 27.66/4.03      ( ~ r1_orders_2(X0,X1,X2)
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 27.66/4.03      | sK0(sK2,sK4,sK5) != X1
% 27.66/4.03      | sK5 != X2
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3015]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41206,plain,
% 27.66/4.03      ( ~ r1_orders_2(X0,X1,sK5)
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 27.66/4.03      | sK0(sK2,sK4,sK5) != X1
% 27.66/4.03      | sK5 != sK5
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41031]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_46366,plain,
% 27.66/4.03      ( ~ r1_orders_2(X0,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 27.66/4.03      | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | sK5 != sK5
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41206]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_46367,plain,
% 27.66/4.03      ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | sK5 != sK5
% 27.66/4.03      | sK2 != X0
% 27.66/4.03      | r1_orders_2(X0,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_46366]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_46369,plain,
% 27.66/4.03      ( sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | sK5 != sK5
% 27.66/4.03      | sK2 != sK2
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5) = iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) != iProver_top ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_46367]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_16,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0) ),
% 27.66/4.03      inference(cnf_transformation,[],[f86]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_857,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_858,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 27.66/4.03      | ~ r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_857]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_41095,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0)
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),X0)
% 27.66/4.03      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_858]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_54796,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 27.66/4.03      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 27.66/4.03      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_41095]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_54797,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5) = iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != iProver_top
% 27.66/4.03      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_54796]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_44268,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,X0,sK5)
% 27.66/4.03      | r2_lattice3(sK2,sK6(sK0(X1,sK4,sK5)),sK5)
% 27.66/4.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.66/4.03      | ~ r1_tarski(sK6(sK0(X1,sK4,sK5)),X0) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_757]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_63330,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 27.66/4.03      | ~ r2_lattice3(sK2,sK3,sK5)
% 27.66/4.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.66/4.03      | ~ r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_44268]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_63331,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5) = iProver_top
% 27.66/4.03      | r2_lattice3(sK2,sK3,sK5) != iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r1_tarski(sK6(sK0(sK2,sK4,sK5)),sK3) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_63330]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_67438,plain,
% 27.66/4.03      ( r1_tarski(X0,k1_tarski(sK5)) != iProver_top
% 27.66/4.03      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.03      | r1_lattice3(sK2,X0,X1) = iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_30813,c_42,c_61,c_63,c_3036,c_4031,c_4034,c_4232,
% 27.66/4.03                 c_4477,c_4760,c_4809,c_4811,c_6519,c_7858,c_25603,
% 27.66/4.03                 c_41225,c_41401,c_43089,c_45515,c_46369,c_54797,c_63331]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_67439,plain,
% 27.66/4.03      ( r1_lattice3(sK2,X0,X1) = iProver_top
% 27.66/4.03      | r2_hidden(X1,sK4) != iProver_top
% 27.66/4.03      | r1_tarski(X0,k1_tarski(sK5)) != iProver_top ),
% 27.66/4.03      inference(renaming,[status(thm)],[c_67438]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_67444,plain,
% 27.66/4.03      ( r1_lattice3(sK2,k1_tarski(X0),X1) = iProver_top
% 27.66/4.03      | r2_hidden(X0,k1_tarski(sK5)) != iProver_top
% 27.66/4.03      | r2_hidden(X1,sK4) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3820,c_67439]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_21,plain,
% 27.66/4.03      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.03      | r1_orders_2(X0,X2,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0) ),
% 27.66/4.03      inference(cnf_transformation,[],[f66]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_772,plain,
% 27.66/4.03      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.03      | r1_orders_2(X0,X2,X1)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_773,plain,
% 27.66/4.03      ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
% 27.66/4.03      | r1_orders_2(sK2,X1,X0)
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_772]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3801,plain,
% 27.66/4.03      ( r1_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X1,X0) = iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_67803,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_67444,c_3801]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68213,plain,
% 27.66/4.03      ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X0,X1) = iProver_top
% 27.66/4.03      | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_67803,c_4543]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68214,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,X1) = iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r2_hidden(X1,k1_tarski(sK5)) != iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.03      inference(renaming,[status(thm)],[c_68213]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68217,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top
% 27.66/4.03      | r2_hidden(sK5,k1_tarski(sK5)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3813,c_68214]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4009,plain,
% 27.66/4.03      ( ~ r2_hidden(X0,sK4) | r1_tarski(k1_tarski(X0),sK4) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4010,plain,
% 27.66/4.03      ( r2_hidden(X0,sK4) != iProver_top
% 27.66/4.03      | r1_tarski(k1_tarski(X0),sK4) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_4009]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3815,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 27.66/4.03      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_25607,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_25274,c_3815]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68243,plain,
% 27.66/4.03      ( r2_hidden(X0,sK4) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X0,sK5) = iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_68217,c_42,c_61,c_3036,c_4010,c_4031,c_4034,c_4232,
% 27.66/4.03                 c_4477,c_4760,c_4809,c_4811,c_6450,c_6519,c_25268,
% 27.66/4.03                 c_25607,c_41225,c_41401,c_43089,c_45515,c_46369,c_54797,
% 27.66/4.03                 c_63331]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68244,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,sK5) = iProver_top
% 27.66/4.03      | r2_hidden(X0,sK4) != iProver_top ),
% 27.66/4.03      inference(renaming,[status(thm)],[c_68243]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68265,plain,
% 27.66/4.03      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_68244,c_3789]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68497,plain,
% 27.66/4.03      ( r2_lattice3(sK2,X0,sK5) = iProver_top
% 27.66/4.03      | r2_hidden(sK0(sK2,X0,sK5),sK4) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_68265,c_61]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68503,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3790,c_68497]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68577,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_68503,c_61]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4,plain,
% 27.66/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.66/4.03      inference(cnf_transformation,[],[f53]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3818,plain,
% 27.66/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.66/4.03      | r1_tarski(X0,X1) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_7,plain,
% 27.66/4.03      ( v1_finset_1(k1_tarski(X0)) ),
% 27.66/4.03      inference(cnf_transformation,[],[f55]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_32,negated_conjecture,
% 27.66/4.03      ( r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 27.66/4.03      | ~ v1_finset_1(X0)
% 27.66/4.03      | k1_xboole_0 = X0 ),
% 27.66/4.03      inference(cnf_transformation,[],[f77]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_534,plain,
% 27.66/4.03      ( r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 27.66/4.03      | k1_tarski(X1) != X0
% 27.66/4.03      | k1_xboole_0 = X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_7,c_32]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_535,plain,
% 27.66/4.03      ( r1_yellow_0(sK2,k1_tarski(X0))
% 27.66/4.03      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 27.66/4.03      | k1_xboole_0 = k1_tarski(X0) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_534]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3806,plain,
% 27.66/4.03      ( k1_xboole_0 = k1_tarski(X0)
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5388,plain,
% 27.66/4.03      ( k1_tarski(X0) = k1_xboole_0
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 27.66/4.03      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3818,c_3806]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_0,plain,
% 27.66/4.03      ( v1_xboole_0(k1_xboole_0) ),
% 27.66/4.03      inference(cnf_transformation,[],[f48]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_1,plain,
% 27.66/4.03      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 27.66/4.03      inference(cnf_transformation,[],[f49]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_507,plain,
% 27.66/4.03      ( k1_tarski(X0) != k1_xboole_0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5393,plain,
% 27.66/4.03      ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 27.66/4.03      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_5388,c_507]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5399,plain,
% 27.66/4.03      ( r1_yellow_0(sK2,k1_tarski(X0)) = iProver_top
% 27.66/4.03      | r2_hidden(X0,sK3) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3820,c_5393]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_15,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0)
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2 ),
% 27.66/4.03      inference(cnf_transformation,[],[f63]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_878,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_879,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.03      | ~ r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.03      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 27.66/4.03      | k1_yellow_0(sK2,X0) = X1 ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_878]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3795,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,X0) = X1
% 27.66/4.03      | r2_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,X0) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_14,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0)
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2 ),
% 27.66/4.03      inference(cnf_transformation,[],[f64]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_899,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_900,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.03      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
% 27.66/4.03      | ~ r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.03      | k1_yellow_0(sK2,X0) = X1 ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_899]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3794,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,X0) = X1
% 27.66/4.03      | r2_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.03      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1)) = iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,X0) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5574,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
% 27.66/4.03      | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(sK1(sK2,k1_tarski(X0),X1),u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3794,c_3799]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_14278,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X1
% 27.66/4.03      | r2_lattice3(sK2,k1_tarski(X0),X1) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X0,sK1(sK2,k1_tarski(X0),X1)) = iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3795,c_5574]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_13,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0)
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2 ),
% 27.66/4.03      inference(cnf_transformation,[],[f65]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_920,plain,
% 27.66/4.03      ( ~ r2_lattice3(X0,X1,X2)
% 27.66/4.03      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 27.66/4.03      | ~ r1_yellow_0(X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | k1_yellow_0(X0,X1) = X2
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_921,plain,
% 27.66/4.03      ( ~ r2_lattice3(sK2,X0,X1)
% 27.66/4.03      | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
% 27.66/4.03      | ~ r1_yellow_0(sK2,X0)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.03      | k1_yellow_0(sK2,X0) = X1 ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_920]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3793,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,X0) = X1
% 27.66/4.03      | r2_lattice3(sK2,X0,X1) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,X1,sK1(sK2,X0,X1)) != iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,X0) != iProver_top
% 27.66/4.03      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_47439,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 27.66/4.03      | r2_lattice3(sK2,k1_tarski(X0),X0) != iProver_top
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_14278,c_3793]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_8,plain,
% 27.66/4.03      ( r1_orders_2(X0,X1,X1)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | v2_struct_0(X0)
% 27.66/4.03      | ~ v3_orders_2(X0)
% 27.66/4.03      | ~ l1_orders_2(X0) ),
% 27.66/4.03      inference(cnf_transformation,[],[f56]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_36,negated_conjecture,
% 27.66/4.03      ( v3_orders_2(sK2) ),
% 27.66/4.03      inference(cnf_transformation,[],[f73]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_513,plain,
% 27.66/4.03      ( r1_orders_2(X0,X1,X1)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | v2_struct_0(X0)
% 27.66/4.03      | ~ l1_orders_2(X0)
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_8,c_36]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_514,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,X0)
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.03      | v2_struct_0(sK2)
% 27.66/4.03      | ~ l1_orders_2(sK2) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_513]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_37,negated_conjecture,
% 27.66/4.03      ( ~ v2_struct_0(sK2) ),
% 27.66/4.03      inference(cnf_transformation,[],[f72]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_518,plain,
% 27.66/4.03      ( r1_orders_2(sK2,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_514,c_37,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_18,plain,
% 27.66/4.03      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.03      | ~ r1_orders_2(X0,X1,X2)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | ~ l1_orders_2(X0) ),
% 27.66/4.03      inference(cnf_transformation,[],[f69]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_824,plain,
% 27.66/4.03      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 27.66/4.03      | ~ r1_orders_2(X0,X1,X2)
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 27.66/4.03      | sK2 != X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_825,plain,
% 27.66/4.03      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 27.66/4.03      | ~ r1_orders_2(sK2,X0,X1)
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_824]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_1495,plain,
% 27.66/4.03      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 27.66/4.03      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 27.66/4.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 27.66/4.03      | X0 != X2
% 27.66/4.03      | X1 != X2
% 27.66/4.03      | sK2 != sK2 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_518,c_825]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_1496,plain,
% 27.66/4.03      ( r2_lattice3(sK2,k1_tarski(X0),X0)
% 27.66/4.03      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_1495]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_1497,plain,
% 27.66/4.03      ( r2_lattice3(sK2,k1_tarski(X0),X0) = iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_47532,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 27.66/4.03      | r1_yellow_0(sK2,k1_tarski(X0)) != iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_47439,c_1497]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_47538,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r2_hidden(X0,sK3) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_5399,c_47532]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_49082,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(X0)) = X0
% 27.66/4.03      | r2_hidden(X0,sK3) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_47538,c_4544]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_49088,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0))) = sK0(sK2,sK3,X0)
% 27.66/4.03      | r2_lattice3(sK2,sK3,X0) = iProver_top
% 27.66/4.03      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3790,c_49082]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_49314,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 27.66/4.03      | r2_lattice3(sK2,sK3,sK5) = iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3813,c_49088]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_49344,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 27.66/4.03      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_49314,c_3815]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68581,plain,
% 27.66/4.03      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_68577,c_49344]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_27,negated_conjecture,
% 27.66/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 27.66/4.03      | ~ v1_finset_1(X0)
% 27.66/4.03      | k1_xboole_0 = X0 ),
% 27.66/4.03      inference(cnf_transformation,[],[f82]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_549,plain,
% 27.66/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 27.66/4.03      | k1_tarski(X1) != X0
% 27.66/4.03      | k1_xboole_0 = X0 ),
% 27.66/4.03      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_550,plain,
% 27.66/4.03      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 27.66/4.03      | k1_xboole_0 = k1_tarski(X0) ),
% 27.66/4.03      inference(unflattening,[status(thm)],[c_549]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3805,plain,
% 27.66/4.03      ( k1_xboole_0 = k1_tarski(X0)
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4541,plain,
% 27.66/4.03      ( m1_subset_1(X0,X1) = iProver_top
% 27.66/4.03      | r2_hidden(X0,X2) != iProver_top
% 27.66/4.03      | r1_tarski(X2,X1) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3818,c_3816]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5489,plain,
% 27.66/4.03      ( k1_tarski(X0) = k1_xboole_0
% 27.66/4.03      | m1_subset_1(k1_yellow_0(sK2,k1_tarski(X0)),X1) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r1_tarski(sK4,X1) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3805,c_4541]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_12555,plain,
% 27.66/4.03      ( m1_subset_1(k1_yellow_0(sK2,k1_tarski(X0)),X1) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r1_tarski(sK4,X1) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_5489,c_507]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_12576,plain,
% 27.66/4.03      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top
% 27.66/4.03      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_12555,c_5198]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4124,plain,
% 27.66/4.03      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3809,c_3817]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_14022,plain,
% 27.66/4.03      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
% 27.66/4.03      | r2_lattice3(sK2,X0,sK5) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_12576,c_4124]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_14023,plain,
% 27.66/4.03      ( r2_lattice3(sK2,X0,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X1)),sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(sK3)) != iProver_top
% 27.66/4.03      | r2_hidden(k1_yellow_0(sK2,k1_tarski(X1)),X0) != iProver_top ),
% 27.66/4.03      inference(renaming,[status(thm)],[c_14022]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_14028,plain,
% 27.66/4.03      ( k1_tarski(X0) = k1_xboole_0
% 27.66/4.03      | r2_lattice3(sK2,sK4,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X0)),sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_3805,c_14023]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_20646,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_tarski(X0)),sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3)) != iProver_top ),
% 27.66/4.03      inference(global_propositional_subsumption,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_14028,c_507]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_68734,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 27.66/4.03      inference(superposition,[status(thm)],[c_68581,c_20646]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_3912,plain,
% 27.66/4.03      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 27.66/4.03      | ~ r1_tarski(k1_tarski(X0),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_4]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5246,plain,
% 27.66/4.03      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 27.66/4.03      | ~ r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3912]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_5247,plain,
% 27.66/4.03      ( m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top
% 27.66/4.03      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_5246]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4105,plain,
% 27.66/4.03      ( ~ r2_hidden(X0,sK3) | r1_tarski(k1_tarski(X0),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4508,plain,
% 27.66/4.03      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 27.66/4.03      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_4105]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4509,plain,
% 27.66/4.03      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 27.66/4.03      | r1_tarski(k1_tarski(sK0(sK2,sK3,sK5)),sK3) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_4508]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4082,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK3,sK5)
% 27.66/4.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.66/4.03      | r2_hidden(sK0(sK2,sK3,sK5),sK3) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3972]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4083,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.66/4.03      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_4082]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4067,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK3,sK5)
% 27.66/4.03      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 27.66/4.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 27.66/4.03      inference(instantiation,[status(thm)],[c_3979]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(c_4071,plain,
% 27.66/4.03      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 27.66/4.03      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
% 27.66/4.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 27.66/4.03      inference(predicate_to_equality,[status(thm)],[c_4067]) ).
% 27.66/4.03  
% 27.66/4.03  cnf(contradiction,plain,
% 27.66/4.03      ( $false ),
% 27.66/4.03      inference(minisat,
% 27.66/4.03                [status(thm)],
% 27.66/4.03                [c_68734,c_68503,c_5247,c_4509,c_4083,c_4071,c_63,c_61]) ).
% 27.66/4.03  
% 27.66/4.03  
% 27.66/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.66/4.03  
% 27.66/4.03  ------                               Statistics
% 27.66/4.03  
% 27.66/4.03  ------ General
% 27.66/4.03  
% 27.66/4.03  abstr_ref_over_cycles:                  0
% 27.66/4.03  abstr_ref_under_cycles:                 0
% 27.66/4.03  gc_basic_clause_elim:                   0
% 27.66/4.03  forced_gc_time:                         0
% 27.66/4.03  parsing_time:                           0.007
% 27.66/4.03  unif_index_cands_time:                  0.
% 27.66/4.03  unif_index_add_time:                    0.
% 27.66/4.03  orderings_time:                         0.
% 27.66/4.03  out_proof_time:                         0.033
% 27.66/4.03  total_time:                             3.08
% 27.66/4.03  num_of_symbols:                         55
% 27.66/4.03  num_of_terms:                           39762
% 27.66/4.03  
% 27.66/4.03  ------ Preprocessing
% 27.66/4.03  
% 27.66/4.03  num_of_splits:                          0
% 27.66/4.03  num_of_split_atoms:                     0
% 27.66/4.03  num_of_reused_defs:                     0
% 27.66/4.03  num_eq_ax_congr_red:                    28
% 27.66/4.03  num_of_sem_filtered_clauses:            1
% 27.66/4.03  num_of_subtypes:                        0
% 27.66/4.03  monotx_restored_types:                  0
% 27.66/4.03  sat_num_of_epr_types:                   0
% 27.66/4.03  sat_num_of_non_cyclic_types:            0
% 27.66/4.03  sat_guarded_non_collapsed_types:        0
% 27.66/4.03  num_pure_diseq_elim:                    0
% 27.66/4.03  simp_replaced_by:                       0
% 27.66/4.03  res_preprocessed:                       166
% 27.66/4.03  prep_upred:                             0
% 27.66/4.03  prep_unflattend:                        142
% 27.66/4.03  smt_new_axioms:                         0
% 27.66/4.03  pred_elim_cands:                        7
% 27.66/4.03  pred_elim:                              5
% 27.66/4.03  pred_elim_cl:                           5
% 27.66/4.03  pred_elim_cycles:                       12
% 27.66/4.03  merged_defs:                            24
% 27.66/4.03  merged_defs_ncl:                        0
% 27.66/4.03  bin_hyper_res:                          24
% 27.66/4.03  prep_cycles:                            4
% 27.66/4.03  pred_elim_time:                         0.027
% 27.66/4.03  splitting_time:                         0.
% 27.66/4.03  sem_filter_time:                        0.
% 27.66/4.03  monotx_time:                            0.
% 27.66/4.03  subtype_inf_time:                       0.
% 27.66/4.03  
% 27.66/4.03  ------ Problem properties
% 27.66/4.03  
% 27.66/4.03  clauses:                                33
% 27.66/4.03  conjectures:                            8
% 27.66/4.03  epr:                                    2
% 27.66/4.03  horn:                                   25
% 27.66/4.03  ground:                                 5
% 27.66/4.03  unary:                                  4
% 27.66/4.03  binary:                                 7
% 27.66/4.03  lits:                                   101
% 27.66/4.03  lits_eq:                                8
% 27.66/4.03  fd_pure:                                0
% 27.66/4.03  fd_pseudo:                              0
% 27.66/4.03  fd_cond:                                0
% 27.66/4.03  fd_pseudo_cond:                         3
% 27.66/4.03  ac_symbols:                             0
% 27.66/4.03  
% 27.66/4.03  ------ Propositional Solver
% 27.66/4.03  
% 27.66/4.03  prop_solver_calls:                      52
% 27.66/4.03  prop_fast_solver_calls:                 7845
% 27.66/4.03  smt_solver_calls:                       0
% 27.66/4.03  smt_fast_solver_calls:                  0
% 27.66/4.03  prop_num_of_clauses:                    31920
% 27.66/4.03  prop_preprocess_simplified:             49717
% 27.66/4.03  prop_fo_subsumed:                       340
% 27.66/4.03  prop_solver_time:                       0.
% 27.66/4.03  smt_solver_time:                        0.
% 27.66/4.03  smt_fast_solver_time:                   0.
% 27.66/4.03  prop_fast_solver_time:                  0.
% 27.66/4.03  prop_unsat_core_time:                   0.002
% 27.66/4.03  
% 27.66/4.03  ------ QBF
% 27.66/4.03  
% 27.66/4.03  qbf_q_res:                              0
% 27.66/4.03  qbf_num_tautologies:                    0
% 27.66/4.03  qbf_prep_cycles:                        0
% 27.66/4.03  
% 27.66/4.03  ------ BMC1
% 27.66/4.03  
% 27.66/4.03  bmc1_current_bound:                     -1
% 27.66/4.03  bmc1_last_solved_bound:                 -1
% 27.66/4.03  bmc1_unsat_core_size:                   -1
% 27.66/4.03  bmc1_unsat_core_parents_size:           -1
% 27.66/4.03  bmc1_merge_next_fun:                    0
% 27.66/4.03  bmc1_unsat_core_clauses_time:           0.
% 27.66/4.03  
% 27.66/4.03  ------ Instantiation
% 27.66/4.03  
% 27.66/4.03  inst_num_of_clauses:                    3024
% 27.66/4.03  inst_num_in_passive:                    448
% 27.66/4.03  inst_num_in_active:                     3753
% 27.66/4.03  inst_num_in_unprocessed:                1067
% 27.66/4.03  inst_num_of_loops:                      4599
% 27.66/4.03  inst_num_of_learning_restarts:          1
% 27.66/4.03  inst_num_moves_active_passive:          832
% 27.66/4.03  inst_lit_activity:                      0
% 27.66/4.03  inst_lit_activity_moves:                2
% 27.66/4.03  inst_num_tautologies:                   0
% 27.66/4.03  inst_num_prop_implied:                  0
% 27.66/4.03  inst_num_existing_simplified:           0
% 27.66/4.03  inst_num_eq_res_simplified:             0
% 27.66/4.03  inst_num_child_elim:                    0
% 27.66/4.03  inst_num_of_dismatching_blockings:      4365
% 27.66/4.03  inst_num_of_non_proper_insts:           9691
% 27.66/4.03  inst_num_of_duplicates:                 0
% 27.66/4.03  inst_inst_num_from_inst_to_res:         0
% 27.66/4.03  inst_dismatching_checking_time:         0.
% 27.66/4.03  
% 27.66/4.03  ------ Resolution
% 27.66/4.03  
% 27.66/4.03  res_num_of_clauses:                     47
% 27.66/4.03  res_num_in_passive:                     47
% 27.66/4.03  res_num_in_active:                      0
% 27.66/4.03  res_num_of_loops:                       170
% 27.66/4.03  res_forward_subset_subsumed:            526
% 27.66/4.03  res_backward_subset_subsumed:           0
% 27.66/4.03  res_forward_subsumed:                   1
% 27.66/4.03  res_backward_subsumed:                  0
% 27.66/4.03  res_forward_subsumption_resolution:     3
% 27.66/4.03  res_backward_subsumption_resolution:    0
% 27.66/4.03  res_clause_to_clause_subsumption:       57579
% 27.66/4.03  res_orphan_elimination:                 0
% 27.66/4.03  res_tautology_del:                      782
% 27.66/4.03  res_num_eq_res_simplified:              0
% 27.66/4.03  res_num_sel_changes:                    0
% 27.66/4.03  res_moves_from_active_to_pass:          0
% 27.66/4.03  
% 27.66/4.03  ------ Superposition
% 27.66/4.03  
% 27.66/4.03  sup_time_total:                         0.
% 27.66/4.03  sup_time_generating:                    0.
% 27.66/4.03  sup_time_sim_full:                      0.
% 27.66/4.03  sup_time_sim_immed:                     0.
% 27.66/4.03  
% 27.66/4.03  sup_num_of_clauses:                     3379
% 27.66/4.03  sup_num_in_active:                      574
% 27.66/4.03  sup_num_in_passive:                     2805
% 27.66/4.03  sup_num_of_loops:                       919
% 27.66/4.03  sup_fw_superposition:                   3616
% 27.66/4.03  sup_bw_superposition:                   3448
% 27.66/4.03  sup_immediate_simplified:               2594
% 27.66/4.03  sup_given_eliminated:                   58
% 27.66/4.03  comparisons_done:                       0
% 27.66/4.03  comparisons_avoided:                    86
% 27.66/4.03  
% 27.66/4.03  ------ Simplifications
% 27.66/4.03  
% 27.66/4.03  
% 27.66/4.03  sim_fw_subset_subsumed:                 345
% 27.66/4.03  sim_bw_subset_subsumed:                 375
% 27.66/4.03  sim_fw_subsumed:                        1749
% 27.66/4.03  sim_bw_subsumed:                        793
% 27.66/4.03  sim_fw_subsumption_res:                 0
% 27.66/4.03  sim_bw_subsumption_res:                 0
% 27.66/4.03  sim_tautology_del:                      16
% 27.66/4.03  sim_eq_tautology_del:                   17
% 27.66/4.03  sim_eq_res_simp:                        11
% 27.66/4.03  sim_fw_demodulated:                     21
% 27.66/4.03  sim_bw_demodulated:                     29
% 27.66/4.03  sim_light_normalised:                   87
% 27.66/4.03  sim_joinable_taut:                      0
% 27.66/4.03  sim_joinable_simp:                      0
% 27.66/4.03  sim_ac_normalised:                      0
% 27.66/4.03  sim_smt_subsumption:                    0
% 27.66/4.03  
%------------------------------------------------------------------------------
