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
% DateTime   : Thu Dec  3 12:21:08 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :  347 (4278 expanded)
%              Number of clauses        :  265 ( 972 expanded)
%              Number of leaves         :   24 (1193 expanded)
%              Depth                    :   46
%              Number of atoms          : 1729 (72007 expanded)
%              Number of equality atoms :  530 (9670 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).

fof(f75,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2780,plain,
    ( ~ r1_orders_2(X0_53,X0_54,X1_54)
    | r1_orders_2(X0_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_29666,plain,
    ( ~ r1_orders_2(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,sK0(sK2,X2_54,sK5),sK5)
    | sK0(sK2,X2_54,sK5) != X0_54
    | sK5 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_29915,plain,
    ( ~ r1_orders_2(sK2,X0_54,sK5)
    | r1_orders_2(sK2,sK0(sK2,X1_54,sK5),sK5)
    | sK0(sK2,X1_54,sK5) != X0_54
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_29666])).

cnf(c_30653,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,X0_54,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_29915])).

cnf(c_30658,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_30653])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_821,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_822,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_2749,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_54),X1_54)
    | ~ r1_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0_54),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_29679,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,X0_54)),X1_54)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),X1_54)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2749])).

cnf(c_29974,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,X0_54)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_29679])).

cnf(c_30115,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_29974])).

cnf(c_2775,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_28126,plain,
    ( sK0(sK2,X0_54,sK5) = sK0(sK2,X0_54,sK5) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_28127,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_28126])).

cnf(c_2778,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3609,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,u1_struct_0(sK2))
    | X2_54 != X0_54
    | u1_struct_0(sK2) != X1_54 ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_3823,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | m1_subset_1(X1_54,u1_struct_0(sK2))
    | X1_54 != X0_54
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3609])).

cnf(c_18476,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2))
    | X0_54 != sK0(sK2,X1_54,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3823])).

cnf(c_27948,plain,
    ( ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))) != sK0(sK2,X0_54,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18476])).

cnf(c_27950,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_27948])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2767,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3492,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2767])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_941,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_942,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_2743,plain,
    ( r2_lattice3(sK2,X0_54,X1_54)
    | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_942])).

cnf(c_3517,plain,
    ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2770,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3489,plain,
    ( r2_hidden(X0_54,X1_54) != iProver_top
    | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_24,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2768,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3491,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

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

cnf(c_704,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_502,c_34])).

cnf(c_705,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_2756,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | r2_lattice3(sK2,X2_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_705])).

cnf(c_3504,plain,
    ( r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r2_lattice3(sK2,X2_54,X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2756])).

cnf(c_4077,plain,
    ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r2_lattice3(sK2,X1_54,sK5) = iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3504])).

cnf(c_4080,plain,
    ( r2_lattice3(sK2,X0_54,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_4077])).

cnf(c_4222,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_4080])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_842,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_843,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_2748,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | ~ r1_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_843])).

cnf(c_3512,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2748])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_926,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_927,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_2744,plain,
    ( r2_lattice3(sK2,X0_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_927])).

cnf(c_3516,plain,
    ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2744])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2766,negated_conjecture,
    ( ~ r2_hidden(X0_54,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3493,plain,
    ( k1_yellow_0(sK2,sK6(X0_54)) = X0_54
    | r2_hidden(X0_54,sK4) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2766])).

cnf(c_4681,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,X1_54))) = sK0(sK2,X0_54,X1_54)
    | r2_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),sK4) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_3493])).

cnf(c_4837,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))) = sK0(sK2,sK4,X0_54)
    | r2_lattice3(sK2,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_4681])).

cnf(c_5506,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r2_lattice3(sK2,sK4,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3512,c_4837])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_905,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_906,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_2745,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,X2_54,X1_54)
    | ~ r2_hidden(X2_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_906])).

cnf(c_3515,plain,
    ( r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_orders_2(sK2,X2_54,X1_54) = iProver_top
    | r2_hidden(X2_54,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2745])).

cnf(c_4867,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r2_lattice3(sK2,X2_54,sK1(sK2,X0_54,X1_54)) != iProver_top
    | r1_orders_2(sK2,X3_54,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_hidden(X3_54,X2_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3512,c_3515])).

cnf(c_8675,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_orders_2(sK2,X2_54,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_hidden(X2_54,sK4) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5506,c_4867])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_884,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_885,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_2746,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | ~ r1_orders_2(sK2,X1_54,sK1(sK2,X0_54,X1_54))
    | ~ r1_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_885])).

cnf(c_3514,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_orders_2(sK2,X1_54,sK1(sK2,X0_54,X1_54)) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_24747,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_hidden(X1_54,sK4) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8675,c_3514])).

cnf(c_24912,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5))
    | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0_54)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4222,c_24747])).

cnf(c_60,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_61,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_62,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2794,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_956,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_957,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_2742,plain,
    ( r2_lattice3(sK2,X0_54,X1_54)
    | ~ r1_orders_2(sK2,sK0(sK2,X0_54,X1_54),X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_957])).

cnf(c_3614,plain,
    ( r2_lattice3(sK2,X0_54,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_3731,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_3732,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3731])).

cnf(c_3620,plain,
    ( r2_lattice3(sK2,X0_54,sK5)
    | r2_hidden(sK0(sK2,X0_54,sK5),X0_54)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_3757,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3758,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3757])).

cnf(c_3604,plain,
    ( r2_lattice3(sK2,X0_54,sK5)
    | m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2744])).

cnf(c_3770,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(c_3771,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3770])).

cnf(c_3586,plain,
    ( ~ r2_hidden(X0_54,sK3)
    | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_3868,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_3869,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3868])).

cnf(c_3661,plain,
    ( ~ r2_lattice3(sK2,X0_54,sK5)
    | r1_orders_2(sK2,X1_54,sK5)
    | ~ r2_hidden(X1_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_3871,plain,
    ( ~ r2_lattice3(sK2,X0_54,sK5)
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_54)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3661])).

cnf(c_3882,plain,
    ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),X0_54) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3871])).

cnf(c_3884,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3882])).

cnf(c_7,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_601,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_602,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_606,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_36,c_34])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_622,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_35])).

cnf(c_623,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_627,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_36,c_34])).

cnf(c_685,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X2
    | X1 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_606,c_627])).

cnf(c_686,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_2757,plain,
    ( r1_orders_2(sK2,X0_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_686])).

cnf(c_2772,plain,
    ( r1_orders_2(sK2,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2757])).

cnf(c_2773,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2757])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2757])).

cnf(c_2926,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0_54,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2772,c_2773,c_2771])).

cnf(c_2927,plain,
    ( r1_orders_2(sK2,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_2926])).

cnf(c_3720,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK0(sK2,X0_54,sK5))
    | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_3918,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3720])).

cnf(c_3919,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3918])).

cnf(c_4,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_547,plain,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_548,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_2759,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_54)),sK4)
    | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_54) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_4114,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2759])).

cnf(c_4115,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4114])).

cnf(c_31,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_532,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_533,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_2760,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0_54))
    | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_54) ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_4113,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_4117,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4113])).

cnf(c_17,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_788,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_789,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_2751,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54)
    | ~ r1_orders_2(sK2,X0_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_3680,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_54),sK0(sK2,X1_54,sK5))
    | ~ r1_orders_2(sK2,X0_54,sK0(sK2,X1_54,sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2751])).

cnf(c_3891,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_54,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,X0_54,sK5))
    | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3680])).

cnf(c_4155,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3891])).

cnf(c_4156,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4155])).

cnf(c_3498,plain,
    ( k1_xboole_0 = k1_tarski(X0_54)
    | r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
    | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2760])).

cnf(c_4175,plain,
    ( k1_tarski(X0_54) = k1_xboole_0
    | r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_3498])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_476,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_2761,plain,
    ( k1_tarski(X0_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_4180,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4175,c_2761])).

cnf(c_6243,plain,
    ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_6663,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_863,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_864,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_2747,plain,
    ( ~ r2_lattice3(sK2,X0_54,X1_54)
    | r2_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54))
    | ~ r1_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_864])).

cnf(c_5991,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2747])).

cnf(c_6775,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5991])).

cnf(c_6776,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6775])).

cnf(c_5993,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2748])).

cnf(c_6788,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5993])).

cnf(c_6789,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6788])).

cnf(c_5992,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | ~ r1_orders_2(sK2,X0_54,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_6803,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5992])).

cnf(c_6804,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6803])).

cnf(c_2776,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_4630,plain,
    ( X0_54 != X1_54
    | sK0(sK2,X2_54,sK5) != X1_54
    | sK0(sK2,X2_54,sK5) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_5485,plain,
    ( X0_54 != sK0(sK2,X1_54,sK5)
    | sK0(sK2,X1_54,sK5) = X0_54
    | sK0(sK2,X1_54,sK5) != sK0(sK2,X1_54,sK5) ),
    inference(instantiation,[status(thm)],[c_4630])).

cnf(c_7781,plain,
    ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
    | sK0(sK2,sK3,sK5) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5485])).

cnf(c_5009,plain,
    ( X0_54 != X1_54
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1_54
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_7668,plain,
    ( X0_54 != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_5009])).

cnf(c_8519,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_7668])).

cnf(c_2779,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | r2_hidden(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3581,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | r2_hidden(X2_54,sK4)
    | X2_54 != X0_54
    | sK4 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_6031,plain,
    ( r2_hidden(X0_54,sK4)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | X0_54 != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3581])).

cnf(c_11507,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6031])).

cnf(c_11508,plain,
    ( sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11507])).

cnf(c_13811,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_18,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_772,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_773,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_2752,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0_54),X1_54)
    | r1_orders_2(sK2,X0_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_773])).

cnf(c_10077,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0_54),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,X0_54,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2752])).

cnf(c_17079,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10077])).

cnf(c_17080,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17079])).

cnf(c_25465,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24912,c_60,c_61,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4115,c_4117,c_4156,c_4180,c_6243,c_6663,c_6776,c_6789,c_6804,c_7781,c_8519,c_11508,c_13811,c_17080])).

cnf(c_25466,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5))
    | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
    | r2_hidden(X0_54,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_25465])).

cnf(c_25471,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,X0_54)),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,X0_54)),sK5))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_54))) = sK5
    | r2_lattice3(sK2,sK3,X0_54) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_25466])).

cnf(c_25834,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK5
    | r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_25471])).

cnf(c_25888,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25834,c_60,c_61,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4115,c_4117,c_4156,c_6243,c_6663,c_6776,c_6789,c_6804,c_7781,c_8519,c_11508,c_13811,c_17080])).

cnf(c_25890,plain,
    ( r2_lattice3(sK2,sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25888])).

cnf(c_5504,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_4837])).

cnf(c_4318,plain,
    ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_orders_2(sK2,X1_54,sK5) = iProver_top
    | r2_hidden(X1_54,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3515])).

cnf(c_4432,plain,
    ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK5) = iProver_top
    | r2_hidden(sK5,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_4318])).

cnf(c_3670,plain,
    ( r1_orders_2(sK2,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_3671,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3670])).

cnf(c_4437,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4432,c_60,c_3671])).

cnf(c_19,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_754,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_755,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_2753,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
    | ~ r1_orders_2(sK2,X1_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_755])).

cnf(c_3507,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_orders_2(sK2,X1_54,X0_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2753])).

cnf(c_22,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_482,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_483,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_720,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_34])).

cnf(c_721,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_2755,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | r1_lattice3(sK2,X2_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_721])).

cnf(c_3505,plain,
    ( r1_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_lattice3(sK2,X2_54,X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2755])).

cnf(c_4105,plain,
    ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_lattice3(sK2,X1_54,sK5) = iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3505])).

cnf(c_4149,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3507,c_4105])).

cnf(c_5045,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,sK5,X1_54) != iProver_top
    | r1_lattice3(sK2,X0_54,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4149,c_60])).

cnf(c_5046,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5045])).

cnf(c_5051,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_54) != iProver_top
    | r2_hidden(X0_54,k1_tarski(X1_54)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_5046])).

cnf(c_5217,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4437,c_5051])).

cnf(c_5222,plain,
    ( r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5217,c_60])).

cnf(c_5223,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5222])).

cnf(c_20,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_736,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_737,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_2754,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
    | r1_orders_2(sK2,X1_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_3506,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) != iProver_top
    | r1_orders_2(sK2,X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2754])).

cnf(c_5228,plain,
    ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5223,c_3506])).

cnf(c_5319,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
    | r1_orders_2(sK2,sK5,X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5228,c_60])).

cnf(c_5320,plain,
    ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5319])).

cnf(c_5326,plain,
    ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,X0_54,X1_54)) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_5320])).

cnf(c_5626,plain,
    ( r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK5),X0_54)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_5326])).

cnf(c_3509,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_orders_2(sK2,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2751])).

cnf(c_3513,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r2_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2747])).

cnf(c_7586,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_orders_2(sK2,X2_54,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_hidden(X2_54,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3513,c_4867])).

cnf(c_7865,plain,
    ( k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_hidden(X1_54,X0_54) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7586,c_3514])).

cnf(c_7880,plain,
    ( k1_yellow_0(sK2,k1_tarski(X0_54)) = X1_54
    | r1_orders_2(sK2,X0_54,X1_54) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(X0_54)) != iProver_top
    | r2_hidden(X1_54,k1_tarski(X0_54)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3509,c_7865])).

cnf(c_8076,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5626,c_7880])).

cnf(c_18430,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8076,c_60])).

cnf(c_18431,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18430])).

cnf(c_18436,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_18431])).

cnf(c_18676,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_18436])).

cnf(c_3508,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54) != iProver_top
    | r1_orders_2(sK2,X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2752])).

cnf(c_18692,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18676,c_3508])).

cnf(c_18717,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18692,c_60])).

cnf(c_18718,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18717])).

cnf(c_18725,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,X1_54)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_54) = X1_54
    | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
    | r1_orders_2(sK2,sK5,sK1(sK2,X0_54,X1_54)) = iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3512,c_18718])).

cnf(c_18869,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_54) = sK5
    | r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18725,c_3514])).

cnf(c_18902,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | k1_yellow_0(sK2,X0_54) = sK5
    | sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18869,c_60])).

cnf(c_18903,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_54) = sK5
    | r2_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_yellow_0(sK2,X0_54) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18902])).

cnf(c_18910,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,sK4,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | k1_yellow_0(sK2,sK4) = sK5
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5504,c_18903])).

cnf(c_19102,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18910,c_60,c_61,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4115,c_4117,c_4156,c_5504,c_6243,c_6663,c_6776,c_6789,c_6804,c_7781,c_8519,c_11508,c_13811,c_17080])).

cnf(c_3657,plain,
    ( ~ r2_lattice3(sK2,X0_54,sK5)
    | r2_lattice3(sK2,X1_54,sK5)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X0_54))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2756])).

cnf(c_4032,plain,
    ( r2_lattice3(sK2,X0_54,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3657])).

cnf(c_18548,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4032])).

cnf(c_18322,plain,
    ( sK0(sK2,X0_54,sK5) != sK0(sK2,X0_54,sK5)
    | sK0(sK2,X0_54,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5))) != sK0(sK2,X0_54,sK5) ),
    inference(instantiation,[status(thm)],[c_5485])).

cnf(c_18334,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_18322])).

cnf(c_4569,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_4169,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_28,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2765,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0_54))
    | ~ r2_hidden(X0_54,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3998,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2764,negated_conjecture,
    ( ~ r2_hidden(X0_54,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0_54),k1_zfmisc_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3999,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_3622,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3616,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_3606,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30658,c_30115,c_28127,c_27950,c_25890,c_19102,c_18548,c_18334,c_4569,c_4169,c_3998,c_3999,c_3622,c_3616,c_3606,c_23,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.59/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/1.98  
% 11.59/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.59/1.98  
% 11.59/1.98  ------  iProver source info
% 11.59/1.98  
% 11.59/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.59/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.59/1.98  git: non_committed_changes: false
% 11.59/1.98  git: last_make_outside_of_git: false
% 11.59/1.98  
% 11.59/1.98  ------ 
% 11.59/1.98  
% 11.59/1.98  ------ Input Options
% 11.59/1.98  
% 11.59/1.98  --out_options                           all
% 11.59/1.98  --tptp_safe_out                         true
% 11.59/1.98  --problem_path                          ""
% 11.59/1.98  --include_path                          ""
% 11.59/1.98  --clausifier                            res/vclausify_rel
% 11.59/1.98  --clausifier_options                    ""
% 11.59/1.98  --stdin                                 false
% 11.59/1.98  --stats_out                             all
% 11.59/1.98  
% 11.59/1.98  ------ General Options
% 11.59/1.98  
% 11.59/1.98  --fof                                   false
% 11.59/1.98  --time_out_real                         305.
% 11.59/1.98  --time_out_virtual                      -1.
% 11.59/1.98  --symbol_type_check                     false
% 11.59/1.98  --clausify_out                          false
% 11.59/1.98  --sig_cnt_out                           false
% 11.59/1.98  --trig_cnt_out                          false
% 11.59/1.98  --trig_cnt_out_tolerance                1.
% 11.59/1.98  --trig_cnt_out_sk_spl                   false
% 11.59/1.98  --abstr_cl_out                          false
% 11.59/1.98  
% 11.59/1.98  ------ Global Options
% 11.59/1.98  
% 11.59/1.98  --schedule                              default
% 11.59/1.98  --add_important_lit                     false
% 11.59/1.98  --prop_solver_per_cl                    1000
% 11.59/1.98  --min_unsat_core                        false
% 11.59/1.98  --soft_assumptions                      false
% 11.59/1.98  --soft_lemma_size                       3
% 11.59/1.98  --prop_impl_unit_size                   0
% 11.59/1.98  --prop_impl_unit                        []
% 11.59/1.98  --share_sel_clauses                     true
% 11.59/1.98  --reset_solvers                         false
% 11.59/1.98  --bc_imp_inh                            [conj_cone]
% 11.59/1.98  --conj_cone_tolerance                   3.
% 11.59/1.98  --extra_neg_conj                        none
% 11.59/1.98  --large_theory_mode                     true
% 11.59/1.98  --prolific_symb_bound                   200
% 11.59/1.98  --lt_threshold                          2000
% 11.59/1.98  --clause_weak_htbl                      true
% 11.59/1.98  --gc_record_bc_elim                     false
% 11.59/1.98  
% 11.59/1.98  ------ Preprocessing Options
% 11.59/1.98  
% 11.59/1.98  --preprocessing_flag                    true
% 11.59/1.98  --time_out_prep_mult                    0.1
% 11.59/1.98  --splitting_mode                        input
% 11.59/1.98  --splitting_grd                         true
% 11.59/1.98  --splitting_cvd                         false
% 11.59/1.98  --splitting_cvd_svl                     false
% 11.59/1.98  --splitting_nvd                         32
% 11.59/1.98  --sub_typing                            true
% 11.59/1.98  --prep_gs_sim                           true
% 11.59/1.98  --prep_unflatten                        true
% 11.59/1.98  --prep_res_sim                          true
% 11.59/1.98  --prep_upred                            true
% 11.59/1.98  --prep_sem_filter                       exhaustive
% 11.59/1.98  --prep_sem_filter_out                   false
% 11.59/1.98  --pred_elim                             true
% 11.59/1.98  --res_sim_input                         true
% 11.59/1.98  --eq_ax_congr_red                       true
% 11.59/1.98  --pure_diseq_elim                       true
% 11.59/1.98  --brand_transform                       false
% 11.59/1.98  --non_eq_to_eq                          false
% 11.59/1.98  --prep_def_merge                        true
% 11.59/1.98  --prep_def_merge_prop_impl              false
% 11.59/1.98  --prep_def_merge_mbd                    true
% 11.59/1.98  --prep_def_merge_tr_red                 false
% 11.59/1.98  --prep_def_merge_tr_cl                  false
% 11.59/1.98  --smt_preprocessing                     true
% 11.59/1.98  --smt_ac_axioms                         fast
% 11.59/1.98  --preprocessed_out                      false
% 11.59/1.98  --preprocessed_stats                    false
% 11.59/1.98  
% 11.59/1.98  ------ Abstraction refinement Options
% 11.59/1.98  
% 11.59/1.98  --abstr_ref                             []
% 11.59/1.98  --abstr_ref_prep                        false
% 11.59/1.98  --abstr_ref_until_sat                   false
% 11.59/1.98  --abstr_ref_sig_restrict                funpre
% 11.59/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/1.98  --abstr_ref_under                       []
% 11.59/1.98  
% 11.59/1.98  ------ SAT Options
% 11.59/1.98  
% 11.59/1.98  --sat_mode                              false
% 11.59/1.98  --sat_fm_restart_options                ""
% 11.59/1.98  --sat_gr_def                            false
% 11.59/1.98  --sat_epr_types                         true
% 11.59/1.98  --sat_non_cyclic_types                  false
% 11.59/1.98  --sat_finite_models                     false
% 11.59/1.98  --sat_fm_lemmas                         false
% 11.59/1.98  --sat_fm_prep                           false
% 11.59/1.98  --sat_fm_uc_incr                        true
% 11.59/1.98  --sat_out_model                         small
% 11.59/1.98  --sat_out_clauses                       false
% 11.59/1.98  
% 11.59/1.98  ------ QBF Options
% 11.59/1.98  
% 11.59/1.98  --qbf_mode                              false
% 11.59/1.98  --qbf_elim_univ                         false
% 11.59/1.98  --qbf_dom_inst                          none
% 11.59/1.98  --qbf_dom_pre_inst                      false
% 11.59/1.98  --qbf_sk_in                             false
% 11.59/1.98  --qbf_pred_elim                         true
% 11.59/1.98  --qbf_split                             512
% 11.59/1.98  
% 11.59/1.98  ------ BMC1 Options
% 11.59/1.98  
% 11.59/1.98  --bmc1_incremental                      false
% 11.59/1.98  --bmc1_axioms                           reachable_all
% 11.59/1.98  --bmc1_min_bound                        0
% 11.59/1.98  --bmc1_max_bound                        -1
% 11.59/1.98  --bmc1_max_bound_default                -1
% 11.59/1.98  --bmc1_symbol_reachability              true
% 11.59/1.98  --bmc1_property_lemmas                  false
% 11.59/1.98  --bmc1_k_induction                      false
% 11.59/1.98  --bmc1_non_equiv_states                 false
% 11.59/1.98  --bmc1_deadlock                         false
% 11.59/1.98  --bmc1_ucm                              false
% 11.59/1.98  --bmc1_add_unsat_core                   none
% 11.59/1.98  --bmc1_unsat_core_children              false
% 11.59/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/1.98  --bmc1_out_stat                         full
% 11.59/1.98  --bmc1_ground_init                      false
% 11.59/1.98  --bmc1_pre_inst_next_state              false
% 11.59/1.98  --bmc1_pre_inst_state                   false
% 11.59/1.98  --bmc1_pre_inst_reach_state             false
% 11.59/1.98  --bmc1_out_unsat_core                   false
% 11.59/1.98  --bmc1_aig_witness_out                  false
% 11.59/1.98  --bmc1_verbose                          false
% 11.59/1.98  --bmc1_dump_clauses_tptp                false
% 11.59/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.59/1.98  --bmc1_dump_file                        -
% 11.59/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.59/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.59/1.98  --bmc1_ucm_extend_mode                  1
% 11.59/1.98  --bmc1_ucm_init_mode                    2
% 11.59/1.98  --bmc1_ucm_cone_mode                    none
% 11.59/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.59/1.98  --bmc1_ucm_relax_model                  4
% 11.59/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.59/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/1.98  --bmc1_ucm_layered_model                none
% 11.59/1.98  --bmc1_ucm_max_lemma_size               10
% 11.59/1.98  
% 11.59/1.98  ------ AIG Options
% 11.59/1.98  
% 11.59/1.98  --aig_mode                              false
% 11.59/1.98  
% 11.59/1.98  ------ Instantiation Options
% 11.59/1.98  
% 11.59/1.98  --instantiation_flag                    true
% 11.59/1.98  --inst_sos_flag                         true
% 11.59/1.98  --inst_sos_phase                        true
% 11.59/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/1.98  --inst_lit_sel_side                     num_symb
% 11.59/1.98  --inst_solver_per_active                1400
% 11.59/1.98  --inst_solver_calls_frac                1.
% 11.59/1.98  --inst_passive_queue_type               priority_queues
% 11.59/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/1.98  --inst_passive_queues_freq              [25;2]
% 11.59/1.98  --inst_dismatching                      true
% 11.59/1.98  --inst_eager_unprocessed_to_passive     true
% 11.59/1.98  --inst_prop_sim_given                   true
% 11.59/1.98  --inst_prop_sim_new                     false
% 11.59/1.98  --inst_subs_new                         false
% 11.59/1.98  --inst_eq_res_simp                      false
% 11.59/1.98  --inst_subs_given                       false
% 11.59/1.98  --inst_orphan_elimination               true
% 11.59/1.98  --inst_learning_loop_flag               true
% 11.59/1.98  --inst_learning_start                   3000
% 11.59/1.98  --inst_learning_factor                  2
% 11.59/1.98  --inst_start_prop_sim_after_learn       3
% 11.59/1.98  --inst_sel_renew                        solver
% 11.59/1.98  --inst_lit_activity_flag                true
% 11.59/1.98  --inst_restr_to_given                   false
% 11.59/1.98  --inst_activity_threshold               500
% 11.59/1.98  --inst_out_proof                        true
% 11.59/1.98  
% 11.59/1.98  ------ Resolution Options
% 11.59/1.98  
% 11.59/1.98  --resolution_flag                       true
% 11.59/1.98  --res_lit_sel                           adaptive
% 11.59/1.98  --res_lit_sel_side                      none
% 11.59/1.98  --res_ordering                          kbo
% 11.59/1.98  --res_to_prop_solver                    active
% 11.59/1.98  --res_prop_simpl_new                    false
% 11.59/1.98  --res_prop_simpl_given                  true
% 11.59/1.98  --res_passive_queue_type                priority_queues
% 11.59/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/1.98  --res_passive_queues_freq               [15;5]
% 11.59/1.98  --res_forward_subs                      full
% 11.59/1.98  --res_backward_subs                     full
% 11.59/1.98  --res_forward_subs_resolution           true
% 11.59/1.98  --res_backward_subs_resolution          true
% 11.59/1.98  --res_orphan_elimination                true
% 11.59/1.98  --res_time_limit                        2.
% 11.59/1.98  --res_out_proof                         true
% 11.59/1.98  
% 11.59/1.98  ------ Superposition Options
% 11.59/1.98  
% 11.59/1.98  --superposition_flag                    true
% 11.59/1.98  --sup_passive_queue_type                priority_queues
% 11.59/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.59/1.98  --demod_completeness_check              fast
% 11.59/1.98  --demod_use_ground                      true
% 11.59/1.98  --sup_to_prop_solver                    passive
% 11.59/1.98  --sup_prop_simpl_new                    true
% 11.59/1.98  --sup_prop_simpl_given                  true
% 11.59/1.98  --sup_fun_splitting                     true
% 11.59/1.98  --sup_smt_interval                      50000
% 11.59/1.98  
% 11.59/1.98  ------ Superposition Simplification Setup
% 11.59/1.98  
% 11.59/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.59/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.59/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.59/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.59/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.59/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.59/1.98  --sup_immed_triv                        [TrivRules]
% 11.59/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_immed_bw_main                     []
% 11.59/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.59/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_input_bw                          []
% 11.59/1.98  
% 11.59/1.98  ------ Combination Options
% 11.59/1.98  
% 11.59/1.98  --comb_res_mult                         3
% 11.59/1.98  --comb_sup_mult                         2
% 11.59/1.98  --comb_inst_mult                        10
% 11.59/1.98  
% 11.59/1.98  ------ Debug Options
% 11.59/1.98  
% 11.59/1.98  --dbg_backtrace                         false
% 11.59/1.98  --dbg_dump_prop_clauses                 false
% 11.59/1.98  --dbg_dump_prop_clauses_file            -
% 11.59/1.98  --dbg_out_stat                          false
% 11.59/1.98  ------ Parsing...
% 11.59/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.59/1.98  
% 11.59/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.59/1.98  
% 11.59/1.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.59/1.98  
% 11.59/1.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.59/1.98  ------ Proving...
% 11.59/1.98  ------ Problem Properties 
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  clauses                                 31
% 11.59/1.98  conjectures                             8
% 11.59/1.98  EPR                                     3
% 11.59/1.98  Horn                                    22
% 11.59/1.98  unary                                   4
% 11.59/1.98  binary                                  5
% 11.59/1.98  lits                                    97
% 11.59/1.98  lits eq                                 8
% 11.59/1.98  fd_pure                                 0
% 11.59/1.98  fd_pseudo                               0
% 11.59/1.98  fd_cond                                 0
% 11.59/1.98  fd_pseudo_cond                          3
% 11.59/1.98  AC symbols                              0
% 11.59/1.98  
% 11.59/1.98  ------ Schedule dynamic 5 is on 
% 11.59/1.98  
% 11.59/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  ------ 
% 11.59/1.98  Current options:
% 11.59/1.98  ------ 
% 11.59/1.98  
% 11.59/1.98  ------ Input Options
% 11.59/1.98  
% 11.59/1.98  --out_options                           all
% 11.59/1.98  --tptp_safe_out                         true
% 11.59/1.98  --problem_path                          ""
% 11.59/1.98  --include_path                          ""
% 11.59/1.98  --clausifier                            res/vclausify_rel
% 11.59/1.98  --clausifier_options                    ""
% 11.59/1.98  --stdin                                 false
% 11.59/1.98  --stats_out                             all
% 11.59/1.98  
% 11.59/1.98  ------ General Options
% 11.59/1.98  
% 11.59/1.98  --fof                                   false
% 11.59/1.98  --time_out_real                         305.
% 11.59/1.98  --time_out_virtual                      -1.
% 11.59/1.98  --symbol_type_check                     false
% 11.59/1.98  --clausify_out                          false
% 11.59/1.98  --sig_cnt_out                           false
% 11.59/1.98  --trig_cnt_out                          false
% 11.59/1.98  --trig_cnt_out_tolerance                1.
% 11.59/1.98  --trig_cnt_out_sk_spl                   false
% 11.59/1.98  --abstr_cl_out                          false
% 11.59/1.98  
% 11.59/1.98  ------ Global Options
% 11.59/1.98  
% 11.59/1.98  --schedule                              default
% 11.59/1.98  --add_important_lit                     false
% 11.59/1.98  --prop_solver_per_cl                    1000
% 11.59/1.98  --min_unsat_core                        false
% 11.59/1.98  --soft_assumptions                      false
% 11.59/1.98  --soft_lemma_size                       3
% 11.59/1.98  --prop_impl_unit_size                   0
% 11.59/1.98  --prop_impl_unit                        []
% 11.59/1.98  --share_sel_clauses                     true
% 11.59/1.98  --reset_solvers                         false
% 11.59/1.98  --bc_imp_inh                            [conj_cone]
% 11.59/1.98  --conj_cone_tolerance                   3.
% 11.59/1.98  --extra_neg_conj                        none
% 11.59/1.98  --large_theory_mode                     true
% 11.59/1.98  --prolific_symb_bound                   200
% 11.59/1.98  --lt_threshold                          2000
% 11.59/1.98  --clause_weak_htbl                      true
% 11.59/1.98  --gc_record_bc_elim                     false
% 11.59/1.98  
% 11.59/1.98  ------ Preprocessing Options
% 11.59/1.98  
% 11.59/1.98  --preprocessing_flag                    true
% 11.59/1.98  --time_out_prep_mult                    0.1
% 11.59/1.98  --splitting_mode                        input
% 11.59/1.98  --splitting_grd                         true
% 11.59/1.98  --splitting_cvd                         false
% 11.59/1.98  --splitting_cvd_svl                     false
% 11.59/1.98  --splitting_nvd                         32
% 11.59/1.98  --sub_typing                            true
% 11.59/1.98  --prep_gs_sim                           true
% 11.59/1.98  --prep_unflatten                        true
% 11.59/1.98  --prep_res_sim                          true
% 11.59/1.98  --prep_upred                            true
% 11.59/1.98  --prep_sem_filter                       exhaustive
% 11.59/1.98  --prep_sem_filter_out                   false
% 11.59/1.98  --pred_elim                             true
% 11.59/1.98  --res_sim_input                         true
% 11.59/1.98  --eq_ax_congr_red                       true
% 11.59/1.98  --pure_diseq_elim                       true
% 11.59/1.98  --brand_transform                       false
% 11.59/1.98  --non_eq_to_eq                          false
% 11.59/1.98  --prep_def_merge                        true
% 11.59/1.98  --prep_def_merge_prop_impl              false
% 11.59/1.98  --prep_def_merge_mbd                    true
% 11.59/1.98  --prep_def_merge_tr_red                 false
% 11.59/1.98  --prep_def_merge_tr_cl                  false
% 11.59/1.98  --smt_preprocessing                     true
% 11.59/1.98  --smt_ac_axioms                         fast
% 11.59/1.98  --preprocessed_out                      false
% 11.59/1.98  --preprocessed_stats                    false
% 11.59/1.98  
% 11.59/1.98  ------ Abstraction refinement Options
% 11.59/1.98  
% 11.59/1.98  --abstr_ref                             []
% 11.59/1.98  --abstr_ref_prep                        false
% 11.59/1.98  --abstr_ref_until_sat                   false
% 11.59/1.98  --abstr_ref_sig_restrict                funpre
% 11.59/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/1.98  --abstr_ref_under                       []
% 11.59/1.98  
% 11.59/1.98  ------ SAT Options
% 11.59/1.98  
% 11.59/1.98  --sat_mode                              false
% 11.59/1.98  --sat_fm_restart_options                ""
% 11.59/1.98  --sat_gr_def                            false
% 11.59/1.98  --sat_epr_types                         true
% 11.59/1.98  --sat_non_cyclic_types                  false
% 11.59/1.98  --sat_finite_models                     false
% 11.59/1.98  --sat_fm_lemmas                         false
% 11.59/1.98  --sat_fm_prep                           false
% 11.59/1.98  --sat_fm_uc_incr                        true
% 11.59/1.98  --sat_out_model                         small
% 11.59/1.98  --sat_out_clauses                       false
% 11.59/1.98  
% 11.59/1.98  ------ QBF Options
% 11.59/1.98  
% 11.59/1.98  --qbf_mode                              false
% 11.59/1.98  --qbf_elim_univ                         false
% 11.59/1.98  --qbf_dom_inst                          none
% 11.59/1.98  --qbf_dom_pre_inst                      false
% 11.59/1.98  --qbf_sk_in                             false
% 11.59/1.98  --qbf_pred_elim                         true
% 11.59/1.98  --qbf_split                             512
% 11.59/1.98  
% 11.59/1.98  ------ BMC1 Options
% 11.59/1.98  
% 11.59/1.98  --bmc1_incremental                      false
% 11.59/1.98  --bmc1_axioms                           reachable_all
% 11.59/1.98  --bmc1_min_bound                        0
% 11.59/1.98  --bmc1_max_bound                        -1
% 11.59/1.98  --bmc1_max_bound_default                -1
% 11.59/1.98  --bmc1_symbol_reachability              true
% 11.59/1.98  --bmc1_property_lemmas                  false
% 11.59/1.98  --bmc1_k_induction                      false
% 11.59/1.98  --bmc1_non_equiv_states                 false
% 11.59/1.98  --bmc1_deadlock                         false
% 11.59/1.98  --bmc1_ucm                              false
% 11.59/1.98  --bmc1_add_unsat_core                   none
% 11.59/1.98  --bmc1_unsat_core_children              false
% 11.59/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/1.98  --bmc1_out_stat                         full
% 11.59/1.98  --bmc1_ground_init                      false
% 11.59/1.98  --bmc1_pre_inst_next_state              false
% 11.59/1.98  --bmc1_pre_inst_state                   false
% 11.59/1.98  --bmc1_pre_inst_reach_state             false
% 11.59/1.98  --bmc1_out_unsat_core                   false
% 11.59/1.98  --bmc1_aig_witness_out                  false
% 11.59/1.98  --bmc1_verbose                          false
% 11.59/1.98  --bmc1_dump_clauses_tptp                false
% 11.59/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.59/1.98  --bmc1_dump_file                        -
% 11.59/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.59/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.59/1.98  --bmc1_ucm_extend_mode                  1
% 11.59/1.98  --bmc1_ucm_init_mode                    2
% 11.59/1.98  --bmc1_ucm_cone_mode                    none
% 11.59/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.59/1.98  --bmc1_ucm_relax_model                  4
% 11.59/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.59/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/1.98  --bmc1_ucm_layered_model                none
% 11.59/1.98  --bmc1_ucm_max_lemma_size               10
% 11.59/1.98  
% 11.59/1.98  ------ AIG Options
% 11.59/1.98  
% 11.59/1.98  --aig_mode                              false
% 11.59/1.98  
% 11.59/1.98  ------ Instantiation Options
% 11.59/1.98  
% 11.59/1.98  --instantiation_flag                    true
% 11.59/1.98  --inst_sos_flag                         true
% 11.59/1.98  --inst_sos_phase                        true
% 11.59/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/1.98  --inst_lit_sel_side                     none
% 11.59/1.98  --inst_solver_per_active                1400
% 11.59/1.98  --inst_solver_calls_frac                1.
% 11.59/1.98  --inst_passive_queue_type               priority_queues
% 11.59/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/1.98  --inst_passive_queues_freq              [25;2]
% 11.59/1.98  --inst_dismatching                      true
% 11.59/1.98  --inst_eager_unprocessed_to_passive     true
% 11.59/1.98  --inst_prop_sim_given                   true
% 11.59/1.98  --inst_prop_sim_new                     false
% 11.59/1.98  --inst_subs_new                         false
% 11.59/1.98  --inst_eq_res_simp                      false
% 11.59/1.98  --inst_subs_given                       false
% 11.59/1.98  --inst_orphan_elimination               true
% 11.59/1.98  --inst_learning_loop_flag               true
% 11.59/1.98  --inst_learning_start                   3000
% 11.59/1.98  --inst_learning_factor                  2
% 11.59/1.98  --inst_start_prop_sim_after_learn       3
% 11.59/1.98  --inst_sel_renew                        solver
% 11.59/1.98  --inst_lit_activity_flag                true
% 11.59/1.98  --inst_restr_to_given                   false
% 11.59/1.98  --inst_activity_threshold               500
% 11.59/1.98  --inst_out_proof                        true
% 11.59/1.98  
% 11.59/1.98  ------ Resolution Options
% 11.59/1.98  
% 11.59/1.98  --resolution_flag                       false
% 11.59/1.98  --res_lit_sel                           adaptive
% 11.59/1.98  --res_lit_sel_side                      none
% 11.59/1.98  --res_ordering                          kbo
% 11.59/1.98  --res_to_prop_solver                    active
% 11.59/1.98  --res_prop_simpl_new                    false
% 11.59/1.98  --res_prop_simpl_given                  true
% 11.59/1.98  --res_passive_queue_type                priority_queues
% 11.59/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/1.98  --res_passive_queues_freq               [15;5]
% 11.59/1.98  --res_forward_subs                      full
% 11.59/1.98  --res_backward_subs                     full
% 11.59/1.98  --res_forward_subs_resolution           true
% 11.59/1.98  --res_backward_subs_resolution          true
% 11.59/1.98  --res_orphan_elimination                true
% 11.59/1.98  --res_time_limit                        2.
% 11.59/1.98  --res_out_proof                         true
% 11.59/1.98  
% 11.59/1.98  ------ Superposition Options
% 11.59/1.98  
% 11.59/1.98  --superposition_flag                    true
% 11.59/1.98  --sup_passive_queue_type                priority_queues
% 11.59/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.59/1.98  --demod_completeness_check              fast
% 11.59/1.98  --demod_use_ground                      true
% 11.59/1.98  --sup_to_prop_solver                    passive
% 11.59/1.98  --sup_prop_simpl_new                    true
% 11.59/1.98  --sup_prop_simpl_given                  true
% 11.59/1.98  --sup_fun_splitting                     true
% 11.59/1.98  --sup_smt_interval                      50000
% 11.59/1.98  
% 11.59/1.98  ------ Superposition Simplification Setup
% 11.59/1.98  
% 11.59/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.59/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.59/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.59/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.59/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.59/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.59/1.98  --sup_immed_triv                        [TrivRules]
% 11.59/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_immed_bw_main                     []
% 11.59/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.59/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/1.98  --sup_input_bw                          []
% 11.59/1.98  
% 11.59/1.98  ------ Combination Options
% 11.59/1.98  
% 11.59/1.98  --comb_res_mult                         3
% 11.59/1.98  --comb_sup_mult                         2
% 11.59/1.98  --comb_inst_mult                        10
% 11.59/1.98  
% 11.59/1.98  ------ Debug Options
% 11.59/1.98  
% 11.59/1.98  --dbg_backtrace                         false
% 11.59/1.98  --dbg_dump_prop_clauses                 false
% 11.59/1.98  --dbg_dump_prop_clauses_file            -
% 11.59/1.98  --dbg_out_stat                          false
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  ------ Proving...
% 11.59/1.98  
% 11.59/1.98  
% 11.59/1.98  % SZS status Theorem for theBenchmark.p
% 11.59/1.98  
% 11.59/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.59/1.98  
% 11.59/1.98  fof(f9,axiom,(
% 11.59/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f25,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(ennf_transformation,[],[f9])).
% 11.59/1.98  
% 11.59/1.98  fof(f26,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(flattening,[],[f25])).
% 11.59/1.98  
% 11.59/1.98  fof(f36,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(nnf_transformation,[],[f26])).
% 11.59/1.98  
% 11.59/1.98  fof(f37,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(flattening,[],[f36])).
% 11.59/1.98  
% 11.59/1.98  fof(f38,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(rectify,[],[f37])).
% 11.59/1.98  
% 11.59/1.98  fof(f39,plain,(
% 11.59/1.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f40,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 11.59/1.98  
% 11.59/1.98  fof(f63,plain,(
% 11.59/1.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f40])).
% 11.59/1.98  
% 11.59/1.98  fof(f87,plain,(
% 11.59/1.98    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(equality_resolution,[],[f63])).
% 11.59/1.98  
% 11.59/1.98  fof(f12,conjecture,(
% 11.59/1.98    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f13,negated_conjecture,(
% 11.59/1.98    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 11.59/1.98    inference(negated_conjecture,[],[f12])).
% 11.59/1.98  
% 11.59/1.98  fof(f14,plain,(
% 11.59/1.98    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 11.59/1.98    inference(rectify,[],[f13])).
% 11.59/1.98  
% 11.59/1.98  fof(f16,plain,(
% 11.59/1.98    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 11.59/1.98    inference(pure_predicate_removal,[],[f14])).
% 11.59/1.98  
% 11.59/1.98  fof(f29,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.59/1.98    inference(ennf_transformation,[],[f16])).
% 11.59/1.98  
% 11.59/1.98  fof(f30,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.59/1.98    inference(flattening,[],[f29])).
% 11.59/1.98  
% 11.59/1.98  fof(f41,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.59/1.98    inference(nnf_transformation,[],[f30])).
% 11.59/1.98  
% 11.59/1.98  fof(f42,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.59/1.98    inference(flattening,[],[f41])).
% 11.59/1.98  
% 11.59/1.98  fof(f43,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.59/1.98    inference(rectify,[],[f42])).
% 11.59/1.98  
% 11.59/1.98  fof(f48,plain,(
% 11.59/1.98    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f47,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f46,plain,(
% 11.59/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f45,plain,(
% 11.59/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f44,plain,(
% 11.59/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f49,plain,(
% 11.59/1.98    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 11.59/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).
% 11.59/1.98  
% 11.59/1.98  fof(f75,plain,(
% 11.59/1.98    l1_orders_2(sK2)),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f84,plain,(
% 11.59/1.98    m1_subset_1(sK5,u1_struct_0(sK2))),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f8,axiom,(
% 11.59/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f23,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(ennf_transformation,[],[f8])).
% 11.59/1.98  
% 11.59/1.98  fof(f24,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(flattening,[],[f23])).
% 11.59/1.98  
% 11.59/1.98  fof(f32,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(nnf_transformation,[],[f24])).
% 11.59/1.98  
% 11.59/1.98  fof(f33,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(rectify,[],[f32])).
% 11.59/1.98  
% 11.59/1.98  fof(f34,plain,(
% 11.59/1.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 11.59/1.98    introduced(choice_axiom,[])).
% 11.59/1.98  
% 11.59/1.98  fof(f35,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 11.59/1.98  
% 11.59/1.98  fof(f60,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f35])).
% 11.59/1.98  
% 11.59/1.98  fof(f3,axiom,(
% 11.59/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f17,plain,(
% 11.59/1.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.59/1.98    inference(ennf_transformation,[],[f3])).
% 11.59/1.98  
% 11.59/1.98  fof(f52,plain,(
% 11.59/1.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f17])).
% 11.59/1.98  
% 11.59/1.98  fof(f85,plain,(
% 11.59/1.98    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f4,axiom,(
% 11.59/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f15,plain,(
% 11.59/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 11.59/1.98    inference(unused_predicate_definition_removal,[],[f4])).
% 11.59/1.98  
% 11.59/1.98  fof(f18,plain,(
% 11.59/1.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.59/1.98    inference(ennf_transformation,[],[f15])).
% 11.59/1.98  
% 11.59/1.98  fof(f53,plain,(
% 11.59/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f18])).
% 11.59/1.98  
% 11.59/1.98  fof(f11,axiom,(
% 11.59/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f28,plain,(
% 11.59/1.98    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(ennf_transformation,[],[f11])).
% 11.59/1.98  
% 11.59/1.98  fof(f72,plain,(
% 11.59/1.98    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f28])).
% 11.59/1.98  
% 11.59/1.98  fof(f64,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f40])).
% 11.59/1.98  
% 11.59/1.98  fof(f59,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f35])).
% 11.59/1.98  
% 11.59/1.98  fof(f82,plain,(
% 11.59/1.98    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f58,plain,(
% 11.59/1.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f35])).
% 11.59/1.98  
% 11.59/1.98  fof(f66,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f40])).
% 11.59/1.98  
% 11.59/1.98  fof(f86,plain,(
% 11.59/1.98    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f61,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f35])).
% 11.59/1.98  
% 11.59/1.98  fof(f7,axiom,(
% 11.59/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f21,plain,(
% 11.59/1.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.59/1.98    inference(ennf_transformation,[],[f7])).
% 11.59/1.98  
% 11.59/1.98  fof(f22,plain,(
% 11.59/1.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.59/1.98    inference(flattening,[],[f21])).
% 11.59/1.98  
% 11.59/1.98  fof(f57,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f22])).
% 11.59/1.98  
% 11.59/1.98  fof(f74,plain,(
% 11.59/1.98    v3_orders_2(sK2)),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f73,plain,(
% 11.59/1.98    ~v2_struct_0(sK2)),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f6,axiom,(
% 11.59/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f19,plain,(
% 11.59/1.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.59/1.98    inference(ennf_transformation,[],[f6])).
% 11.59/1.98  
% 11.59/1.98  fof(f20,plain,(
% 11.59/1.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.59/1.98    inference(flattening,[],[f19])).
% 11.59/1.98  
% 11.59/1.98  fof(f31,plain,(
% 11.59/1.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.59/1.98    inference(nnf_transformation,[],[f20])).
% 11.59/1.98  
% 11.59/1.98  fof(f55,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f31])).
% 11.59/1.98  
% 11.59/1.98  fof(f5,axiom,(
% 11.59/1.98    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f54,plain,(
% 11.59/1.98    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f5])).
% 11.59/1.98  
% 11.59/1.98  fof(f83,plain,(
% 11.59/1.98    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f78,plain,(
% 11.59/1.98    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f10,axiom,(
% 11.59/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f27,plain,(
% 11.59/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.59/1.98    inference(ennf_transformation,[],[f10])).
% 11.59/1.98  
% 11.59/1.98  fof(f70,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f27])).
% 11.59/1.98  
% 11.59/1.98  fof(f1,axiom,(
% 11.59/1.98    v1_xboole_0(k1_xboole_0)),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f50,plain,(
% 11.59/1.98    v1_xboole_0(k1_xboole_0)),
% 11.59/1.98    inference(cnf_transformation,[],[f1])).
% 11.59/1.98  
% 11.59/1.98  fof(f2,axiom,(
% 11.59/1.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 11.59/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/1.98  
% 11.59/1.98  fof(f51,plain,(
% 11.59/1.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f2])).
% 11.59/1.98  
% 11.59/1.98  fof(f65,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f40])).
% 11.59/1.98  
% 11.59/1.98  fof(f69,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f27])).
% 11.59/1.98  
% 11.59/1.98  fof(f68,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f27])).
% 11.59/1.98  
% 11.59/1.98  fof(f71,plain,(
% 11.59/1.98    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f28])).
% 11.59/1.98  
% 11.59/1.98  fof(f67,plain,(
% 11.59/1.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.59/1.98    inference(cnf_transformation,[],[f27])).
% 11.59/1.98  
% 11.59/1.98  fof(f81,plain,(
% 11.59/1.98    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  fof(f80,plain,(
% 11.59/1.98    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.59/1.98    inference(cnf_transformation,[],[f49])).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2780,plain,
% 11.59/1.98      ( ~ r1_orders_2(X0_53,X0_54,X1_54)
% 11.59/1.98      | r1_orders_2(X0_53,X2_54,X3_54)
% 11.59/1.98      | X2_54 != X0_54
% 11.59/1.98      | X3_54 != X1_54 ),
% 11.59/1.98      theory(equality) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_29666,plain,
% 11.59/1.98      ( ~ r1_orders_2(sK2,X0_54,X1_54)
% 11.59/1.98      | r1_orders_2(sK2,sK0(sK2,X2_54,sK5),sK5)
% 11.59/1.98      | sK0(sK2,X2_54,sK5) != X0_54
% 11.59/1.98      | sK5 != X1_54 ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_2780]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_29915,plain,
% 11.59/1.98      ( ~ r1_orders_2(sK2,X0_54,sK5)
% 11.59/1.98      | r1_orders_2(sK2,sK0(sK2,X1_54,sK5),sK5)
% 11.59/1.98      | sK0(sK2,X1_54,sK5) != X0_54
% 11.59/1.98      | sK5 != sK5 ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_29666]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_30653,plain,
% 11.59/1.98      ( r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK5)
% 11.59/1.98      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 11.59/1.98      | sK0(sK2,X0_54,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.59/1.98      | sK5 != sK5 ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_29915]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_30658,plain,
% 11.59/1.98      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.59/1.98      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 11.59/1.98      | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.59/1.98      | sK5 != sK5 ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_30653]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_15,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 11.59/1.98      | ~ r1_yellow_0(X0,X1)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 11.59/1.98      | ~ l1_orders_2(X0) ),
% 11.59/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_34,negated_conjecture,
% 11.59/1.98      ( l1_orders_2(sK2) ),
% 11.59/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_821,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 11.59/1.98      | ~ r1_yellow_0(X0,X1)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 11.59/1.98      | sK2 != X0 ),
% 11.59/1.98      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_822,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 11.59/1.98      | ~ r1_yellow_0(sK2,X0)
% 11.59/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 11.59/1.98      inference(unflattening,[status(thm)],[c_821]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2749,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,X0_54),X1_54)
% 11.59/1.98      | ~ r1_yellow_0(sK2,X0_54)
% 11.59/1.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,X0_54),u1_struct_0(sK2)) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_822]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_29679,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,X0_54)),X1_54)
% 11.59/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),X1_54)
% 11.59/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54)))
% 11.59/1.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),u1_struct_0(sK2)) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_2749]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_29974,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,X0_54)),sK5)
% 11.59/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),sK5)
% 11.59/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54)))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))),u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_29679]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_30115,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.59/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 11.59/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.59/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_29974]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2775,plain,( X0_54 = X0_54 ),theory(equality) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_28126,plain,
% 11.59/1.98      ( sK0(sK2,X0_54,sK5) = sK0(sK2,X0_54,sK5) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_28127,plain,
% 11.59/1.98      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_28126]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2778,plain,
% 11.59/1.98      ( ~ m1_subset_1(X0_54,X1_54)
% 11.59/1.98      | m1_subset_1(X2_54,X3_54)
% 11.59/1.98      | X2_54 != X0_54
% 11.59/1.98      | X3_54 != X1_54 ),
% 11.59/1.98      theory(equality) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3609,plain,
% 11.59/1.98      ( ~ m1_subset_1(X0_54,X1_54)
% 11.59/1.98      | m1_subset_1(X2_54,u1_struct_0(sK2))
% 11.59/1.98      | X2_54 != X0_54
% 11.59/1.98      | u1_struct_0(sK2) != X1_54 ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_2778]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3823,plain,
% 11.59/1.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.98      | m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.98      | X1_54 != X0_54
% 11.59/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_3609]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_18476,plain,
% 11.59/1.98      ( m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2))
% 11.59/1.98      | X0_54 != sK0(sK2,X1_54,sK5)
% 11.59/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_3823]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_27948,plain,
% 11.59/1.98      ( ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 11.59/1.98      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))),u1_struct_0(sK2))
% 11.59/1.98      | k1_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))) != sK0(sK2,X0_54,sK5)
% 11.59/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_18476]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_27950,plain,
% 11.59/1.98      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.59/1.98      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 11.59/1.98      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 11.59/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.59/1.98      inference(instantiation,[status(thm)],[c_27948]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_25,negated_conjecture,
% 11.59/1.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2767,negated_conjecture,
% 11.59/1.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_25]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3492,plain,
% 11.59/1.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.59/1.98      inference(predicate_to_equality,[status(thm)],[c_2767]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_9,plain,
% 11.59/1.98      ( r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ l1_orders_2(X0) ),
% 11.59/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_941,plain,
% 11.59/1.98      ( r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | sK2 != X0 ),
% 11.59/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_942,plain,
% 11.59/1.98      ( r2_lattice3(sK2,X0,X1)
% 11.59/1.98      | r2_hidden(sK0(sK2,X0,X1),X0)
% 11.59/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(unflattening,[status(thm)],[c_941]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2743,plain,
% 11.59/1.98      ( r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.98      | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54)
% 11.59/1.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_942]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3517,plain,
% 11.59/1.98      ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
% 11.59/1.98      | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54) = iProver_top
% 11.59/1.98      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.98      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2,plain,
% 11.59/1.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 11.59/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2770,plain,
% 11.59/1.98      ( ~ r2_hidden(X0_54,X1_54)
% 11.59/1.98      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3489,plain,
% 11.59/1.98      ( r2_hidden(X0_54,X1_54) != iProver_top
% 11.59/1.98      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) = iProver_top ),
% 11.59/1.98      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_24,negated_conjecture,
% 11.59/1.98      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 11.59/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2768,negated_conjecture,
% 11.59/1.98      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_24]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3491,plain,
% 11.59/1.98      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.59/1.98      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3,plain,
% 11.59/1.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.59/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_21,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_lattice3(X0,X3,X2)
% 11.59/1.98      | ~ r1_tarski(X3,X1)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ l1_orders_2(X0) ),
% 11.59/1.98      inference(cnf_transformation,[],[f72]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_501,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_lattice3(X0,X3,X2)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.59/1.98      | ~ l1_orders_2(X0)
% 11.59/1.98      | X3 != X4
% 11.59/1.98      | X1 != X5 ),
% 11.59/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_502,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_lattice3(X0,X3,X2)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.59/1.98      | ~ l1_orders_2(X0) ),
% 11.59/1.98      inference(unflattening,[status(thm)],[c_501]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_704,plain,
% 11.59/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.98      | r2_lattice3(X0,X3,X2)
% 11.59/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.59/1.98      | sK2 != X0 ),
% 11.59/1.98      inference(resolution_lifted,[status(thm)],[c_502,c_34]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_705,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.98      | r2_lattice3(sK2,X2,X1)
% 11.59/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 11.59/1.98      inference(unflattening,[status(thm)],[c_704]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_2756,plain,
% 11.59/1.98      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.98      | r2_lattice3(sK2,X2_54,X1_54)
% 11.59/1.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.98      | ~ m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) ),
% 11.59/1.98      inference(subtyping,[status(esa)],[c_705]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_3504,plain,
% 11.59/1.98      ( r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.98      | r2_lattice3(sK2,X2_54,X1_54) = iProver_top
% 11.59/1.98      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.98      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 11.59/1.98      inference(predicate_to_equality,[status(thm)],[c_2756]) ).
% 11.59/1.98  
% 11.59/1.98  cnf(c_4077,plain,
% 11.59/1.98      ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.98      | r2_lattice3(sK2,X1_54,sK5) = iProver_top
% 11.59/1.98      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 11.59/1.98      inference(superposition,[status(thm)],[c_3492,c_3504]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4080,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5) = iProver_top
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3491,c_4077]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4222,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3489,c_4080]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_14,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.59/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_842,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_843,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_842]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2748,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = X1_54 ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_843]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3512,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2748]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_10,plain,
% 11.59/1.99      ( r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_926,plain,
% 11.59/1.99      ( r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_927,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_926]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2744,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_927]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3516,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2744]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_27,negated_conjecture,
% 11.59/1.99      ( ~ r2_hidden(X0,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 11.59/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2766,negated_conjecture,
% 11.59/1.99      ( ~ r2_hidden(X0_54,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,sK6(X0_54)) = X0_54 ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_27]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3493,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(X0_54)) = X0_54
% 11.59/1.99      | r2_hidden(X0_54,sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2766]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4681,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,X1_54))) = sK0(sK2,X0_54,X1_54)
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) = iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,X0_54,X1_54),sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3516,c_3493]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4837,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))) = sK0(sK2,sK4,X0_54)
% 11.59/1.99      | r2_lattice3(sK2,sK4,X0_54) = iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3517,c_4681]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5506,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3512,c_4837]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_11,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_orders_2(X0,X3,X2)
% 11.59/1.99      | ~ r2_hidden(X3,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_905,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_orders_2(X0,X3,X2)
% 11.59/1.99      | ~ r2_hidden(X3,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_906,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | r1_orders_2(sK2,X2,X1)
% 11.59/1.99      | ~ r2_hidden(X2,X0)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_905]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2745,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | r1_orders_2(sK2,X2_54,X1_54)
% 11.59/1.99      | ~ r2_hidden(X2_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X2_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_906]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3515,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X2_54,X1_54) = iProver_top
% 11.59/1.99      | r2_hidden(X2_54,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2745]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4867,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,X2_54,sK1(sK2,X0_54,X1_54)) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X3_54,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_hidden(X3_54,X2_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3512,c_3515]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_8675,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X2_54,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_hidden(X2_54,sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_5506,c_4867]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_12,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.59/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_884,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_885,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_884]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2746,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ r1_orders_2(sK2,X1_54,sK1(sK2,X0_54,X1_54))
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = X1_54 ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_885]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3514,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X1_54,sK1(sK2,X0_54,X1_54)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_24747,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,X0_54,X1_54)))) = sK0(sK2,sK4,sK1(sK2,X0_54,X1_54))
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_hidden(X1_54,sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_8675,c_3514]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_24912,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(X0_54)) != iProver_top
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top
% 11.59/1.99      | r2_hidden(sK5,sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_4222,c_24747]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_60,plain,
% 11.59/1.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_61,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_23,negated_conjecture,
% 11.59/1.99      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 11.59/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_62,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2794,plain,
% 11.59/1.99      ( sK4 = sK4 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_8,plain,
% 11.59/1.99      ( r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_956,plain,
% 11.59/1.99      ( r2_lattice3(X0,X1,X2)
% 11.59/1.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_957,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_956]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2742,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0_54,X1_54),X1_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_957]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3614,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK5)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2742]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3731,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3614]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3732,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3731]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3620,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | r2_hidden(sK0(sK2,X0_54,sK5),X0_54)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2743]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3757,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.59/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3620]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3758,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3757]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3604,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2744]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3770,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3604]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3771,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3770]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3586,plain,
% 11.59/1.99      ( ~ r2_hidden(X0_54,sK3)
% 11.59/1.99      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2770]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3868,plain,
% 11.59/1.99      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 11.59/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3586]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3869,plain,
% 11.59/1.99      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 11.59/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3868]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3661,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | r1_orders_2(sK2,X1_54,sK5)
% 11.59/1.99      | ~ r2_hidden(X1_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2745]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3871,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 11.59/1.99      | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_54)
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3661]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3882,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,sK3,sK5),X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3871]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3884,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3882]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7,plain,
% 11.59/1.99      ( r3_orders_2(X0,X1,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | v2_struct_0(X0)
% 11.59/1.99      | ~ v3_orders_2(X0)
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_35,negated_conjecture,
% 11.59/1.99      ( v3_orders_2(sK2) ),
% 11.59/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_601,plain,
% 11.59/1.99      ( r3_orders_2(X0,X1,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | v2_struct_0(X0)
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_7,c_35]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_602,plain,
% 11.59/1.99      ( r3_orders_2(sK2,X0,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | v2_struct_0(sK2)
% 11.59/1.99      | ~ l1_orders_2(sK2) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_601]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_36,negated_conjecture,
% 11.59/1.99      ( ~ v2_struct_0(sK2) ),
% 11.59/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_606,plain,
% 11.59/1.99      ( r3_orders_2(sK2,X0,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_602,c_36,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6,plain,
% 11.59/1.99      ( r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ r3_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | v2_struct_0(X0)
% 11.59/1.99      | ~ v3_orders_2(X0)
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_622,plain,
% 11.59/1.99      ( r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ r3_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | v2_struct_0(X0)
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_35]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_623,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ r3_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | v2_struct_0(sK2)
% 11.59/1.99      | ~ l1_orders_2(sK2) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_622]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_627,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ r3_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_623,c_36,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_685,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | X0 != X2
% 11.59/1.99      | X1 != X2
% 11.59/1.99      | sK2 != sK2 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_606,c_627]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_686,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_685]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2757,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_686]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2772,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ sP1_iProver_split ),
% 11.59/1.99      inference(splitting,
% 11.59/1.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 11.59/1.99                [c_2757]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2773,plain,
% 11.59/1.99      ( sP1_iProver_split | sP0_iProver_split ),
% 11.59/1.99      inference(splitting,
% 11.59/1.99                [splitting(split),new_symbols(definition,[])],
% 11.59/1.99                [c_2757]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2771,plain,
% 11.59/1.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 11.59/1.99      inference(splitting,
% 11.59/1.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.59/1.99                [c_2757]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2926,plain,
% 11.59/1.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | r1_orders_2(sK2,X0_54,X0_54) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_2772,c_2773,c_2771]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2927,plain,
% 11.59/1.99      ( r1_orders_2(sK2,X0_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_2926]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3720,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK0(sK2,X0_54,sK5))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2927]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3918,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3720]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3919,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) = iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3918]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4,plain,
% 11.59/1.99      ( v1_finset_1(k1_tarski(X0)) ),
% 11.59/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_26,negated_conjecture,
% 11.59/1.99      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 11.59/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.59/1.99      | ~ v1_finset_1(X0)
% 11.59/1.99      | k1_xboole_0 = X0 ),
% 11.59/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_547,plain,
% 11.59/1.99      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 11.59/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_tarski(X1) != X0
% 11.59/1.99      | k1_xboole_0 = X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_548,plain,
% 11.59/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(X0) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_547]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2759,plain,
% 11.59/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_54)),sK4)
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(X0_54) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_548]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4114,plain,
% 11.59/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2759]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4115,plain,
% 11.59/1.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 11.59/1.99      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
% 11.59/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_4114]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_31,negated_conjecture,
% 11.59/1.99      ( r1_yellow_0(sK2,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.59/1.99      | ~ v1_finset_1(X0)
% 11.59/1.99      | k1_xboole_0 = X0 ),
% 11.59/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_532,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_tarski(X1) != X0
% 11.59/1.99      | k1_xboole_0 = X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_31]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_533,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,k1_tarski(X0))
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(X0) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_532]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2760,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,k1_tarski(X0_54))
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(X0_54) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_533]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4113,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 11.59/1.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2760]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4117,plain,
% 11.59/1.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 11.59/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_4113]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_17,plain,
% 11.59/1.99      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_788,plain,
% 11.59/1.99      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_789,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 11.59/1.99      | ~ r1_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_788]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2751,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 11.59/1.99      | ~ r1_orders_2(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_789]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3680,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0_54),sK0(sK2,X1_54,sK5))
% 11.59/1.99      | ~ r1_orders_2(sK2,X0_54,sK0(sK2,X1_54,sK5))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2751]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3891,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_54,sK5))
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,X0_54,sK5))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3680]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4155,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3891]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4156,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_4155]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3498,plain,
% 11.59/1.99      ( k1_xboole_0 = k1_tarski(X0_54)
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
% 11.59/1.99      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2760]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4175,plain,
% 11.59/1.99      ( k1_tarski(X0_54) = k1_xboole_0
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3489,c_3498]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_0,plain,
% 11.59/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_1,plain,
% 11.59/1.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 11.59/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_476,plain,
% 11.59/1.99      ( k1_tarski(X0) != k1_xboole_0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2761,plain,
% 11.59/1.99      ( k1_tarski(X0_54) != k1_xboole_0 ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_476]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4180,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,k1_tarski(X0_54)) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_4175,c_2761]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6243,plain,
% 11.59/1.99      ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6663,plain,
% 11.59/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_13,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.59/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_863,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.59/1.99      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 11.59/1.99      | ~ r1_yellow_0(X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | k1_yellow_0(X0,X1) = X2
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_864,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.59/1.99      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_863]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2747,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | r2_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54))
% 11.59/1.99      | ~ r1_yellow_0(sK2,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = X1_54 ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_864]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5991,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2747]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6775,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5991]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6776,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_6775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5993,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2748]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6788,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5993]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6789,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.59/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_6788]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5992,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 11.59/1.99      | ~ r1_orders_2(sK2,X0_54,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2746]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6803,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5992]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6804,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_6803]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2776,plain,
% 11.59/1.99      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 11.59/1.99      theory(equality) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4630,plain,
% 11.59/1.99      ( X0_54 != X1_54
% 11.59/1.99      | sK0(sK2,X2_54,sK5) != X1_54
% 11.59/1.99      | sK0(sK2,X2_54,sK5) = X0_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2776]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5485,plain,
% 11.59/1.99      ( X0_54 != sK0(sK2,X1_54,sK5)
% 11.59/1.99      | sK0(sK2,X1_54,sK5) = X0_54
% 11.59/1.99      | sK0(sK2,X1_54,sK5) != sK0(sK2,X1_54,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_4630]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7781,plain,
% 11.59/1.99      ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
% 11.59/1.99      | sK0(sK2,sK3,sK5) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5485]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5009,plain,
% 11.59/1.99      ( X0_54 != X1_54
% 11.59/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) != X1_54
% 11.59/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2776]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7668,plain,
% 11.59/1.99      ( X0_54 != k1_tarski(sK0(sK2,sK3,sK5))
% 11.59/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54
% 11.59/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5009]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_8519,plain,
% 11.59/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 11.59/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 11.59/1.99      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_7668]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2779,plain,
% 11.59/1.99      ( ~ r2_hidden(X0_54,X1_54)
% 11.59/1.99      | r2_hidden(X2_54,X3_54)
% 11.59/1.99      | X2_54 != X0_54
% 11.59/1.99      | X3_54 != X1_54 ),
% 11.59/1.99      theory(equality) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3581,plain,
% 11.59/1.99      ( ~ r2_hidden(X0_54,X1_54)
% 11.59/1.99      | r2_hidden(X2_54,sK4)
% 11.59/1.99      | X2_54 != X0_54
% 11.59/1.99      | sK4 != X1_54 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2779]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_6031,plain,
% 11.59/1.99      ( r2_hidden(X0_54,sK4)
% 11.59/1.99      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.59/1.99      | X0_54 != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | sK4 != sK4 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3581]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_11507,plain,
% 11.59/1.99      ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
% 11.59/1.99      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.59/1.99      | sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | sK4 != sK4 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_6031]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_11508,plain,
% 11.59/1.99      ( sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.59/1.99      | sK4 != sK4
% 11.59/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
% 11.59/1.99      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_11507]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_13811,plain,
% 11.59/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2761]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_772,plain,
% 11.59/1.99      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | r1_orders_2(X0,X1,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_773,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 11.59/1.99      | r1_orders_2(sK2,X0,X1)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_772]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2752,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 11.59/1.99      | r1_orders_2(sK2,X0_54,X1_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_773]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_10077,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0_54),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | r1_orders_2(sK2,X0_54,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2752]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_17079,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.59/1.99      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_10077]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_17080,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
% 11.59/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_17079]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25465,plain,
% 11.59/1.99      ( r2_hidden(sK5,sK4) != iProver_top
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_24912,c_60,c_61,c_62,c_2794,c_3732,c_3758,c_3771,
% 11.59/1.99                 c_3869,c_3884,c_3919,c_4115,c_4117,c_4156,c_4180,c_6243,
% 11.59/1.99                 c_6663,c_6776,c_6789,c_6804,c_7781,c_8519,c_11508,
% 11.59/1.99                 c_13811,c_17080]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25466,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(X0_54),sK5))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(X0_54)) = sK5
% 11.59/1.99      | r2_hidden(X0_54,sK3) != iProver_top
% 11.59/1.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_25465]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25471,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,X0_54)),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,X0_54)),sK5))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,X0_54))) = sK5
% 11.59/1.99      | r2_lattice3(sK2,sK3,X0_54) = iProver_top
% 11.59/1.99      | r2_hidden(sK5,sK4) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3517,c_25466]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25834,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5)))) = sK0(sK2,sK4,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK5))
% 11.59/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK5
% 11.59/1.99      | r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.59/1.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3492,c_25471]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25888,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_25834,c_60,c_61,c_2794,c_3732,c_3758,c_3771,c_3869,
% 11.59/1.99                 c_3884,c_3919,c_4115,c_4117,c_4156,c_6243,c_6663,c_6776,
% 11.59/1.99                 c_6789,c_6804,c_7781,c_8519,c_11508,c_13811,c_17080]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_25890,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK3,sK5) ),
% 11.59/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_25888]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5504,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 11.59/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3492,c_4837]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4318,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X1_54,sK5) = iProver_top
% 11.59/1.99      | r2_hidden(X1_54,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3492,c_3515]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4432,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,sK5) = iProver_top
% 11.59/1.99      | r2_hidden(sK5,X0_54) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3492,c_4318]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3670,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK5,sK5) | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2927]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3671,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK5,sK5) = iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_3670]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4437,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK5,sK5) = iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_4432,c_60,c_3671]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_19,plain,
% 11.59/1.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X2,X1)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_754,plain,
% 11.59/1.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | ~ r1_orders_2(X0,X2,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_755,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0),X1)
% 11.59/1.99      | ~ r1_orders_2(sK2,X1,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_754]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2753,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 11.59/1.99      | ~ r1_orders_2(sK2,X1_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_755]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3507,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X1_54,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2753]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_22,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_lattice3(X0,X3,X2)
% 11.59/1.99      | ~ r1_tarski(X3,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_482,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_lattice3(X0,X3,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.59/1.99      | ~ l1_orders_2(X0)
% 11.59/1.99      | X3 != X4
% 11.59/1.99      | X1 != X5 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_483,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_lattice3(X0,X3,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_720,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.59/1.99      | r1_lattice3(X0,X3,X2)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_483,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_721,plain,
% 11.59/1.99      ( ~ r1_lattice3(sK2,X0,X1)
% 11.59/1.99      | r1_lattice3(sK2,X2,X1)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_720]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2755,plain,
% 11.59/1.99      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 11.59/1.99      | r1_lattice3(sK2,X2_54,X1_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_721]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3505,plain,
% 11.59/1.99      ( r1_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_lattice3(sK2,X2_54,X1_54) = iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2755]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4105,plain,
% 11.59/1.99      ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_lattice3(sK2,X1_54,sK5) = iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3492,c_3505]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4149,plain,
% 11.59/1.99      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X1_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3507,c_4105]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5045,plain,
% 11.59/1.99      ( m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X1_54) != iProver_top
% 11.59/1.99      | r1_lattice3(sK2,X0_54,sK5) = iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_4149,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5046,plain,
% 11.59/1.99      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X1_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_5045]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5051,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X1_54) != iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(X1_54)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3489,c_5046]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5217,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_4437,c_5051]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5222,plain,
% 11.59/1.99      ( r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_5217,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5223,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_5222]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_20,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | r1_orders_2(X0,X2,X1)
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ l1_orders_2(X0) ),
% 11.59/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_736,plain,
% 11.59/1.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 11.59/1.99      | r1_orders_2(X0,X2,X1)
% 11.59/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.59/1.99      | sK2 != X0 ),
% 11.59/1.99      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_737,plain,
% 11.59/1.99      ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
% 11.59/1.99      | r1_orders_2(sK2,X1,X0)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(unflattening,[status(thm)],[c_736]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2754,plain,
% 11.59/1.99      ( ~ r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 11.59/1.99      | r1_orders_2(sK2,X1_54,X0_54)
% 11.59/1.99      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_737]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3506,plain,
% 11.59/1.99      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X1_54,X0_54) = iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2754]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5228,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_5223,c_3506]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5319,plain,
% 11.59/1.99      ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X0_54) = iProver_top ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_5228,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5320,plain,
% 11.59/1.99      ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 11.59/1.99      | r2_hidden(X0_54,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_5319]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5326,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,X1_54) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,sK0(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,X0_54,X1_54),k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3516,c_5320]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_5626,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK5),X0_54)) = iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3517,c_5326]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3509,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2751]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3513,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2747]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7586,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X2_54,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_hidden(X2_54,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3513,c_4867]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7865,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_hidden(X1_54,X0_54) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_7586,c_3514]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_7880,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,k1_tarski(X0_54)) = X1_54
% 11.59/1.99      | r1_orders_2(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(X0_54)) != iProver_top
% 11.59/1.99      | r2_hidden(X1_54,k1_tarski(X0_54)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3509,c_7865]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_8076,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_5626,c_7880]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18430,plain,
% 11.59/1.99      ( m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_8076,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18431,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r2_hidden(sK0(sK2,k1_tarski(sK5),X0_54),k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_18430]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18436,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_54),u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3517,c_18431]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18676,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3516,c_18436]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3508,plain,
% 11.59/1.99      ( r2_lattice3(sK2,k1_tarski(X0_54),X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,X0_54,X1_54) = iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(predicate_to_equality,[status(thm)],[c_2752]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18692,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_18676,c_3508]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18717,plain,
% 11.59/1.99      ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 11.59/1.99      | sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_18692,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18718,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),X0_54) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_18717]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18725,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,X1_54)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = X1_54
% 11.59/1.99      | r2_lattice3(sK2,X0_54,X1_54) != iProver_top
% 11.59/1.99      | r1_orders_2(sK2,sK5,sK1(sK2,X0_54,X1_54)) = iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_3512,c_18718]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18869,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = sK5
% 11.59/1.99      | r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_18725,c_3514]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18902,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = sK5
% 11.59/1.99      | sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_18869,c_60]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18903,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_54,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | k1_yellow_0(sK2,X0_54) = sK5
% 11.59/1.99      | r2_lattice3(sK2,X0_54,sK5) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,X0_54) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top ),
% 11.59/1.99      inference(renaming,[status(thm)],[c_18902]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18910,plain,
% 11.59/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,sK4,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 11.59/1.99      | k1_yellow_0(sK2,sK4) = sK5
% 11.59/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.59/1.99      | r1_yellow_0(sK2,sK4) != iProver_top ),
% 11.59/1.99      inference(superposition,[status(thm)],[c_5504,c_18903]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_19102,plain,
% 11.59/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
% 11.59/1.99      inference(global_propositional_subsumption,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_18910,c_60,c_61,c_62,c_2794,c_3732,c_3758,c_3771,
% 11.59/1.99                 c_3869,c_3884,c_3919,c_4115,c_4117,c_4156,c_5504,c_6243,
% 11.59/1.99                 c_6663,c_6776,c_6789,c_6804,c_7781,c_8519,c_11508,
% 11.59/1.99                 c_13811,c_17080]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3657,plain,
% 11.59/1.99      ( ~ r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | r2_lattice3(sK2,X1_54,sK5)
% 11.59/1.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X0_54))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2756]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4032,plain,
% 11.59/1.99      ( r2_lattice3(sK2,X0_54,sK5)
% 11.59/1.99      | ~ r2_lattice3(sK2,sK3,sK5)
% 11.59/1.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(sK3))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3657]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18548,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.59/1.99      | ~ r2_lattice3(sK2,sK3,sK5)
% 11.59/1.99      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_4032]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18322,plain,
% 11.59/1.99      ( sK0(sK2,X0_54,sK5) != sK0(sK2,X0_54,sK5)
% 11.59/1.99      | sK0(sK2,X0_54,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5)))
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5))) != sK0(sK2,X0_54,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_5485]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_18334,plain,
% 11.59/1.99      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 11.59/1.99      | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.59/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_18322]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4569,plain,
% 11.59/1.99      ( sK5 = sK5 ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_4169,plain,
% 11.59/1.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_28,negated_conjecture,
% 11.59/1.99      ( r1_yellow_0(sK2,sK6(X0))
% 11.59/1.99      | ~ r2_hidden(X0,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2765,negated_conjecture,
% 11.59/1.99      ( r1_yellow_0(sK2,sK6(X0_54))
% 11.59/1.99      | ~ r2_hidden(X0_54,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_28]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3998,plain,
% 11.59/1.99      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.59/1.99      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2765]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_29,negated_conjecture,
% 11.59/1.99      ( ~ r2_hidden(X0,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 11.59/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_2764,negated_conjecture,
% 11.59/1.99      ( ~ r2_hidden(X0_54,sK4)
% 11.59/1.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK6(X0_54),k1_zfmisc_1(sK3)) ),
% 11.59/1.99      inference(subtyping,[status(esa)],[c_29]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3999,plain,
% 11.59/1.99      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.59/1.99      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.59/1.99      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_2764]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3622,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.59/1.99      | r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3620]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3616,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.59/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3614]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(c_3606,plain,
% 11.59/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.59/1.99      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.59/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.59/1.99      inference(instantiation,[status(thm)],[c_3604]) ).
% 11.59/1.99  
% 11.59/1.99  cnf(contradiction,plain,
% 11.59/1.99      ( $false ),
% 11.59/1.99      inference(minisat,
% 11.59/1.99                [status(thm)],
% 11.59/1.99                [c_30658,c_30115,c_28127,c_27950,c_25890,c_19102,c_18548,
% 11.59/1.99                 c_18334,c_4569,c_4169,c_3998,c_3999,c_3622,c_3616,
% 11.59/1.99                 c_3606,c_23,c_25]) ).
% 11.59/1.99  
% 11.59/1.99  
% 11.59/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.59/1.99  
% 11.59/1.99  ------                               Statistics
% 11.59/1.99  
% 11.59/1.99  ------ General
% 11.59/1.99  
% 11.59/1.99  abstr_ref_over_cycles:                  0
% 11.59/1.99  abstr_ref_under_cycles:                 0
% 11.59/1.99  gc_basic_clause_elim:                   0
% 11.59/1.99  forced_gc_time:                         0
% 11.59/1.99  parsing_time:                           0.011
% 11.59/1.99  unif_index_cands_time:                  0.
% 11.59/1.99  unif_index_add_time:                    0.
% 11.59/1.99  orderings_time:                         0.
% 11.59/1.99  out_proof_time:                         0.023
% 11.59/1.99  total_time:                             1.271
% 11.59/1.99  num_of_symbols:                         57
% 11.59/1.99  num_of_terms:                           20843
% 11.59/1.99  
% 11.59/1.99  ------ Preprocessing
% 11.59/1.99  
% 11.59/1.99  num_of_splits:                          2
% 11.59/1.99  num_of_split_atoms:                     2
% 11.59/1.99  num_of_reused_defs:                     0
% 11.59/1.99  num_eq_ax_congr_red:                    38
% 11.59/1.99  num_of_sem_filtered_clauses:            3
% 11.59/1.99  num_of_subtypes:                        2
% 11.59/1.99  monotx_restored_types:                  0
% 11.59/1.99  sat_num_of_epr_types:                   0
% 11.59/1.99  sat_num_of_non_cyclic_types:            0
% 11.59/1.99  sat_guarded_non_collapsed_types:        1
% 11.59/1.99  num_pure_diseq_elim:                    0
% 11.59/1.99  simp_replaced_by:                       0
% 11.59/1.99  res_preprocessed:                       147
% 11.59/1.99  prep_upred:                             0
% 11.59/1.99  prep_unflattend:                        114
% 11.59/1.99  smt_new_axioms:                         0
% 11.59/1.99  pred_elim_cands:                        6
% 11.59/1.99  pred_elim:                              7
% 11.59/1.99  pred_elim_cl:                           8
% 11.59/1.99  pred_elim_cycles:                       11
% 11.59/1.99  merged_defs:                            8
% 11.59/1.99  merged_defs_ncl:                        0
% 11.59/1.99  bin_hyper_res:                          8
% 11.59/1.99  prep_cycles:                            4
% 11.59/1.99  pred_elim_time:                         0.038
% 11.59/1.99  splitting_time:                         0.
% 11.59/1.99  sem_filter_time:                        0.
% 11.59/1.99  monotx_time:                            0.
% 11.59/1.99  subtype_inf_time:                       0.
% 11.59/1.99  
% 11.59/1.99  ------ Problem properties
% 11.59/1.99  
% 11.59/1.99  clauses:                                31
% 11.59/1.99  conjectures:                            8
% 11.59/1.99  epr:                                    3
% 11.59/1.99  horn:                                   22
% 11.59/1.99  ground:                                 6
% 11.59/1.99  unary:                                  4
% 11.59/1.99  binary:                                 5
% 11.59/1.99  lits:                                   97
% 11.59/1.99  lits_eq:                                8
% 11.59/1.99  fd_pure:                                0
% 11.59/1.99  fd_pseudo:                              0
% 11.59/1.99  fd_cond:                                0
% 11.59/1.99  fd_pseudo_cond:                         3
% 11.59/1.99  ac_symbols:                             0
% 11.59/1.99  
% 11.59/1.99  ------ Propositional Solver
% 11.59/1.99  
% 11.59/1.99  prop_solver_calls:                      43
% 11.59/1.99  prop_fast_solver_calls:                 7343
% 11.59/1.99  smt_solver_calls:                       0
% 11.59/1.99  smt_fast_solver_calls:                  0
% 11.59/1.99  prop_num_of_clauses:                    14318
% 11.59/1.99  prop_preprocess_simplified:             21150
% 11.59/1.99  prop_fo_subsumed:                       293
% 11.59/1.99  prop_solver_time:                       0.
% 11.59/1.99  smt_solver_time:                        0.
% 11.59/1.99  smt_fast_solver_time:                   0.
% 11.59/1.99  prop_fast_solver_time:                  0.
% 11.59/1.99  prop_unsat_core_time:                   0.001
% 11.59/1.99  
% 11.59/1.99  ------ QBF
% 11.59/1.99  
% 11.59/1.99  qbf_q_res:                              0
% 11.59/1.99  qbf_num_tautologies:                    0
% 11.59/1.99  qbf_prep_cycles:                        0
% 11.59/1.99  
% 11.59/1.99  ------ BMC1
% 11.59/1.99  
% 11.59/1.99  bmc1_current_bound:                     -1
% 11.59/1.99  bmc1_last_solved_bound:                 -1
% 11.59/1.99  bmc1_unsat_core_size:                   -1
% 11.59/1.99  bmc1_unsat_core_parents_size:           -1
% 11.59/1.99  bmc1_merge_next_fun:                    0
% 11.59/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.59/1.99  
% 11.59/1.99  ------ Instantiation
% 11.59/1.99  
% 11.59/1.99  inst_num_of_clauses:                    204
% 11.59/1.99  inst_num_in_passive:                    49
% 11.59/1.99  inst_num_in_active:                     2293
% 11.59/1.99  inst_num_in_unprocessed:                24
% 11.59/1.99  inst_num_of_loops:                      3135
% 11.59/1.99  inst_num_of_learning_restarts:          1
% 11.59/1.99  inst_num_moves_active_passive:          828
% 11.59/1.99  inst_lit_activity:                      0
% 11.59/1.99  inst_lit_activity_moves:                1
% 11.59/1.99  inst_num_tautologies:                   0
% 11.59/1.99  inst_num_prop_implied:                  0
% 11.59/1.99  inst_num_existing_simplified:           0
% 11.59/1.99  inst_num_eq_res_simplified:             0
% 11.59/1.99  inst_num_child_elim:                    0
% 11.59/1.99  inst_num_of_dismatching_blockings:      2157
% 11.59/1.99  inst_num_of_non_proper_insts:           5441
% 11.59/1.99  inst_num_of_duplicates:                 0
% 11.59/1.99  inst_inst_num_from_inst_to_res:         0
% 11.59/1.99  inst_dismatching_checking_time:         0.
% 11.59/1.99  
% 11.59/1.99  ------ Resolution
% 11.59/1.99  
% 11.59/1.99  res_num_of_clauses:                     39
% 11.59/1.99  res_num_in_passive:                     39
% 11.59/1.99  res_num_in_active:                      0
% 11.59/1.99  res_num_of_loops:                       151
% 11.59/1.99  res_forward_subset_subsumed:            199
% 11.59/1.99  res_backward_subset_subsumed:           0
% 11.59/1.99  res_forward_subsumed:                   0
% 11.59/1.99  res_backward_subsumed:                  0
% 11.59/1.99  res_forward_subsumption_resolution:     3
% 11.59/1.99  res_backward_subsumption_resolution:    0
% 11.59/1.99  res_clause_to_clause_subsumption:       9221
% 11.59/1.99  res_orphan_elimination:                 0
% 11.59/1.99  res_tautology_del:                      488
% 11.59/1.99  res_num_eq_res_simplified:              0
% 11.59/1.99  res_num_sel_changes:                    0
% 11.59/1.99  res_moves_from_active_to_pass:          0
% 11.59/1.99  
% 11.59/1.99  ------ Superposition
% 11.59/1.99  
% 11.59/1.99  sup_time_total:                         0.
% 11.59/1.99  sup_time_generating:                    0.
% 11.59/1.99  sup_time_sim_full:                      0.
% 11.59/1.99  sup_time_sim_immed:                     0.
% 11.59/1.99  
% 11.59/1.99  sup_num_of_clauses:                     928
% 11.59/1.99  sup_num_in_active:                      444
% 11.59/1.99  sup_num_in_passive:                     484
% 11.59/1.99  sup_num_of_loops:                       626
% 11.59/1.99  sup_fw_superposition:                   680
% 11.59/1.99  sup_bw_superposition:                   709
% 11.59/1.99  sup_immediate_simplified:               264
% 11.59/1.99  sup_given_eliminated:                   1
% 11.59/1.99  comparisons_done:                       0
% 11.59/1.99  comparisons_avoided:                    218
% 11.59/1.99  
% 11.59/1.99  ------ Simplifications
% 11.59/1.99  
% 11.59/1.99  
% 11.59/1.99  sim_fw_subset_subsumed:                 130
% 11.59/1.99  sim_bw_subset_subsumed:                 165
% 11.59/1.99  sim_fw_subsumed:                        68
% 11.59/1.99  sim_bw_subsumed:                        122
% 11.59/1.99  sim_fw_subsumption_res:                 0
% 11.59/1.99  sim_bw_subsumption_res:                 0
% 11.59/1.99  sim_tautology_del:                      5
% 11.59/1.99  sim_eq_tautology_del:                   0
% 11.59/1.99  sim_eq_res_simp:                        0
% 11.59/1.99  sim_fw_demodulated:                     0
% 11.59/1.99  sim_bw_demodulated:                     1
% 11.59/1.99  sim_light_normalised:                   2
% 11.59/1.99  sim_joinable_taut:                      0
% 11.59/1.99  sim_joinable_simp:                      0
% 11.59/1.99  sim_ac_normalised:                      0
% 11.59/1.99  sim_smt_subsumption:                    0
% 11.59/1.99  
%------------------------------------------------------------------------------
