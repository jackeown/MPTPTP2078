%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:10 EST 2020

% Result     : Theorem 19.64s
% Output     : CNFRefutation 19.64s
% Verified   : 
% Statistics : Number of formulae       :  326 (12225 expanded)
%              Number of clauses        :  247 (2950 expanded)
%              Number of leaves         :   24 (3354 expanded)
%              Depth                    :   62
%              Number of atoms          : 1758 (200174 expanded)
%              Number of equality atoms :  643 (27102 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
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
    inference(pure_predicate_removal,[],[f14])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
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
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
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
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).

fof(f75,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    ( r1_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X7] :
      ( r2_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | r1_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X5] :
      ( k2_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    ! [X5] :
      ( r2_yellow_0(sK2,sK6(X5))
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

cnf(c_29402,plain,
    ( ~ r1_orders_2(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | sK0(sK2,sK4,sK5) != X1_54
    | sK5 != X0_54 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_29658,plain,
    ( ~ r1_orders_2(sK2,sK5,X0_54)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | sK0(sK2,sK4,sK5) != X0_54
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_29402])).

cnf(c_30304,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_29658])).

cnf(c_15,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_821,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_822,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_2749,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,X1_54,k2_yellow_0(sK2,X0_54))
    | ~ r2_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0_54),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_29473,plain,
    ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0_54)
    | r1_orders_2(sK2,X0_54,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2749])).

cnf(c_29869,plain,
    ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
    | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_29473])).

cnf(c_2775,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_28079,plain,
    ( sK0(sK2,X0_54,sK5) = sK0(sK2,X0_54,sK5) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_28080,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_28079])).

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

cnf(c_18440,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2))
    | X0_54 != sK0(sK2,X1_54,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3823])).

cnf(c_27767,plain,
    ( ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))) != sK0(sK2,X0_54,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18440])).

cnf(c_27769,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_27767])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_941,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_942,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_2743,plain,
    ( r1_lattice3(sK2,X0_54,X1_54)
    | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_942])).

cnf(c_3517,plain,
    ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_10,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_926,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_927,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_2744,plain,
    ( r1_lattice3(sK2,X0_54,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_927])).

cnf(c_3516,plain,
    ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2744])).

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
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2768,negated_conjecture,
    ( r1_lattice3(sK2,sK3,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3491,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2767,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3492,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2767])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

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

cnf(c_4153,plain,
    ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_lattice3(sK2,X1_54,sK5) = iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3505])).

cnf(c_4156,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_4153])).

cnf(c_4229,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_4156])).

cnf(c_4237,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_54,sK3) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4229,c_4153])).

cnf(c_5639,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,k1_tarski(X1_54)) != iProver_top
    | r2_hidden(X1_54,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_4237])).

cnf(c_5666,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_5639])).

cnf(c_6664,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_54,sK3) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5666,c_4153])).

cnf(c_7237,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54))) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_6664])).

cnf(c_7279,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_7237])).

cnf(c_9607,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_54,sK3) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7279,c_4153])).

cnf(c_10951,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54))) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_9607])).

cnf(c_11541,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_10951])).

cnf(c_12912,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)),X4_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_54,sK3) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)),X4_54)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11541,c_4153])).

cnf(c_13645,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54)),X4_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54)),X4_54))) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_12912])).

cnf(c_13992,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)),sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_13645])).

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

cnf(c_15864,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13992,c_3506])).

cnf(c_60,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( ~ r1_lattice3(sK2,sK3,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_62,plain,
    ( r1_lattice3(sK2,sK3,sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2794,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_956,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_957,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_2742,plain,
    ( r1_lattice3(sK2,X0_54,X1_54)
    | ~ r1_orders_2(sK2,X1_54,sK0(sK2,X0_54,X1_54))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_957])).

cnf(c_3614,plain,
    ( r1_lattice3(sK2,X0_54,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,X0_54,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_3731,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_3732,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3731])).

cnf(c_3620,plain,
    ( r1_lattice3(sK2,X0_54,sK5)
    | r2_hidden(sK0(sK2,X0_54,sK5),X0_54)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_3757,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3758,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3757])).

cnf(c_3604,plain,
    ( r1_lattice3(sK2,X0_54,sK5)
    | m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2744])).

cnf(c_3770,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(c_3771,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
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

cnf(c_11,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_905,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_906,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_2745,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | r1_orders_2(sK2,X1_54,X2_54)
    | ~ r2_hidden(X2_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_906])).

cnf(c_3661,plain,
    ( ~ r1_lattice3(sK2,X0_54,sK5)
    | r1_orders_2(sK2,sK5,X1_54)
    | ~ r2_hidden(X1_54,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_3871,plain,
    ( ~ r1_lattice3(sK2,X0_54,sK5)
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
    | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_54)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3661])).

cnf(c_3882,plain,
    ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),X0_54) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3871])).

cnf(c_3884,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
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
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_547,plain,
    ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_548,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_2759,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_54)),sK4)
    | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_54) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_4120,plain,
    ( r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2759])).

cnf(c_4121,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4120])).

cnf(c_31,negated_conjecture,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_532,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_31])).

cnf(c_533,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_2760,plain,
    ( r2_yellow_0(sK2,k1_tarski(X0_54))
    | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_54) ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_4119,plain,
    ( r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_4123,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4119])).

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

cnf(c_3678,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK0(sK2,X1_54,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,X1_54,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_3893,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_54,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3678])).

cnf(c_4168,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3893])).

cnf(c_4169,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4168])).

cnf(c_6237,plain,
    ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_6659,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_13,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_863,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_864,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_2747,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | r1_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54))
    | ~ r2_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_864])).

cnf(c_6004,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2747])).

cnf(c_6772,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_6004])).

cnf(c_6773,plain,
    ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6772])).

cnf(c_14,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_842,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_843,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_2748,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | ~ r2_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_843])).

cnf(c_6006,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2748])).

cnf(c_6785,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_6006])).

cnf(c_6786,plain,
    ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6785])).

cnf(c_12,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_884,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_885,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_2746,plain,
    ( ~ r1_lattice3(sK2,X0_54,X1_54)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_54,X1_54),X1_54)
    | ~ r2_yellow_0(sK2,X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_885])).

cnf(c_6005,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
    | ~ r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),X0_54)
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_6800,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_6005])).

cnf(c_6801,plain,
    ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6800])).

cnf(c_2776,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_4640,plain,
    ( X0_54 != X1_54
    | sK0(sK2,X2_54,sK5) != X1_54
    | sK0(sK2,X2_54,sK5) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_5460,plain,
    ( X0_54 != sK0(sK2,X1_54,sK5)
    | sK0(sK2,X1_54,sK5) = X0_54
    | sK0(sK2,X1_54,sK5) != sK0(sK2,X1_54,sK5) ),
    inference(instantiation,[status(thm)],[c_4640])).

cnf(c_7783,plain,
    ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
    | sK0(sK2,sK3,sK5) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5460])).

cnf(c_4999,plain,
    ( X0_54 != X1_54
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1_54
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_7670,plain,
    ( X0_54 != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_4999])).

cnf(c_8519,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_7670])).

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

cnf(c_6044,plain,
    ( r2_hidden(X0_54,sK4)
    | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | X0_54 != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3581])).

cnf(c_11459,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
    | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | sK0(sK2,sK3,sK5) != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6044])).

cnf(c_11460,plain,
    ( sK0(sK2,sK3,sK5) != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11459])).

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

cnf(c_13834,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_10053,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0_54),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2754])).

cnf(c_17015,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10053])).

cnf(c_17016,plain,
    ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17015])).

cnf(c_18329,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15864,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,c_17016])).

cnf(c_18330,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18329])).

cnf(c_18335,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_18330])).

cnf(c_3518,plain,
    ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r1_orders_2(sK2,X1_54,sK0(sK2,X0_54,X1_54)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2742])).

cnf(c_18340,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18335,c_3518])).

cnf(c_18497,plain,
    ( m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18340,c_60])).

cnf(c_18498,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18497])).

cnf(c_18504,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18498,c_3506])).

cnf(c_12911,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11541,c_3506])).

cnf(c_15727,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12911,c_60])).

cnf(c_15728,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15727])).

cnf(c_15733,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_15728])).

cnf(c_18653,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18504,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,c_15733,c_17016])).

cnf(c_18659,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18653,c_3518])).

cnf(c_18671,plain,
    ( m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18659,c_60])).

cnf(c_18672,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18671])).

cnf(c_18678,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18672,c_3506])).

cnf(c_9606,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7279,c_3506])).

cnf(c_12775,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9606,c_60])).

cnf(c_12776,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12775])).

cnf(c_12781,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_12776])).

cnf(c_18703,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18678,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,c_6786,c_6801,c_7783,c_8519,c_11460,c_12781,c_13834,c_17016])).

cnf(c_18709,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18703,c_3518])).

cnf(c_18842,plain,
    ( m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18709,c_60])).

cnf(c_18843,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18842])).

cnf(c_18849,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18843,c_3506])).

cnf(c_6663,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5666,c_3506])).

cnf(c_9110,plain,
    ( m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6663,c_60])).

cnf(c_9111,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9110])).

cnf(c_9116,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_9111])).

cnf(c_18878,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18849,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,c_6786,c_6801,c_7783,c_8519,c_9116,c_11460,c_13834,c_17016])).

cnf(c_18884,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18878,c_3518])).

cnf(c_18898,plain,
    ( r2_hidden(X0_54,sK3) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18884,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,c_3884,c_3919,c_4121,c_4123,c_4169,c_4229,c_6237,c_6659,c_6773,c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,c_17016])).

cnf(c_18899,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_18898])).

cnf(c_18905,plain,
    ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18899,c_3506])).

cnf(c_19089,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | r1_orders_2(sK2,sK5,X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18905,c_60])).

cnf(c_19090,plain,
    ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
    | r2_hidden(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19089])).

cnf(c_19096,plain,
    ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,X0_54,X1_54)) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),sK3) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_19090])).

cnf(c_19246,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19096,c_3518])).

cnf(c_19261,plain,
    ( r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top
    | r1_lattice3(sK2,X0_54,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19246,c_60])).

cnf(c_19262,plain,
    ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_19261])).

cnf(c_19265,plain,
    ( r1_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_19262])).

cnf(c_19266,plain,
    ( r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19265])).

cnf(c_3653,plain,
    ( ~ r1_lattice3(sK2,X0_54,sK5)
    | r1_lattice3(sK2,X1_54,sK5)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X0_54))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2755])).

cnf(c_4032,plain,
    ( r1_lattice3(sK2,X0_54,sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3653])).

cnf(c_18536,plain,
    ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r1_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4032])).

cnf(c_18298,plain,
    ( sK0(sK2,X0_54,sK5) != sK0(sK2,X0_54,sK5)
    | sK0(sK2,X0_54,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5))) != sK0(sK2,X0_54,sK5) ),
    inference(instantiation,[status(thm)],[c_5460])).

cnf(c_18310,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_18298])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2766,negated_conjecture,
    ( ~ r2_hidden(X0_54,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK6(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3493,plain,
    ( k2_yellow_0(sK2,sK6(X0_54)) = X0_54
    | r2_hidden(X0_54,sK4) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2766])).

cnf(c_4835,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,X1_54))) = sK0(sK2,X0_54,X1_54)
    | r1_lattice3(sK2,X0_54,X1_54) = iProver_top
    | r2_hidden(sK0(sK2,X0_54,X1_54),sK4) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_3493])).

cnf(c_4957,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))) = sK0(sK2,sK4,X0_54)
    | r1_lattice3(sK2,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_4835])).

cnf(c_5152,plain,
    ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_4957])).

cnf(c_4575,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_4176,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_28,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2765,negated_conjecture,
    ( r2_yellow_0(sK2,sK6(X0_54))
    | ~ r2_hidden(X0_54,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3998,plain,
    ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
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
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3616,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_3606,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30304,c_29869,c_28080,c_27769,c_19266,c_19265,c_18536,c_18310,c_5152,c_4575,c_4176,c_3998,c_3999,c_3622,c_3616,c_3606,c_62,c_23,c_60,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:19:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.64/3.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.64/3.02  
% 19.64/3.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.64/3.02  
% 19.64/3.02  ------  iProver source info
% 19.64/3.02  
% 19.64/3.02  git: date: 2020-06-30 10:37:57 +0100
% 19.64/3.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.64/3.02  git: non_committed_changes: false
% 19.64/3.02  git: last_make_outside_of_git: false
% 19.64/3.02  
% 19.64/3.02  ------ 
% 19.64/3.02  
% 19.64/3.02  ------ Input Options
% 19.64/3.02  
% 19.64/3.02  --out_options                           all
% 19.64/3.02  --tptp_safe_out                         true
% 19.64/3.02  --problem_path                          ""
% 19.64/3.02  --include_path                          ""
% 19.64/3.02  --clausifier                            res/vclausify_rel
% 19.64/3.02  --clausifier_options                    ""
% 19.64/3.02  --stdin                                 false
% 19.64/3.02  --stats_out                             all
% 19.64/3.02  
% 19.64/3.02  ------ General Options
% 19.64/3.02  
% 19.64/3.02  --fof                                   false
% 19.64/3.02  --time_out_real                         305.
% 19.64/3.02  --time_out_virtual                      -1.
% 19.64/3.02  --symbol_type_check                     false
% 19.64/3.02  --clausify_out                          false
% 19.64/3.02  --sig_cnt_out                           false
% 19.64/3.02  --trig_cnt_out                          false
% 19.64/3.02  --trig_cnt_out_tolerance                1.
% 19.64/3.02  --trig_cnt_out_sk_spl                   false
% 19.64/3.02  --abstr_cl_out                          false
% 19.64/3.02  
% 19.64/3.02  ------ Global Options
% 19.64/3.02  
% 19.64/3.02  --schedule                              default
% 19.64/3.02  --add_important_lit                     false
% 19.64/3.02  --prop_solver_per_cl                    1000
% 19.64/3.02  --min_unsat_core                        false
% 19.64/3.02  --soft_assumptions                      false
% 19.64/3.02  --soft_lemma_size                       3
% 19.64/3.02  --prop_impl_unit_size                   0
% 19.64/3.02  --prop_impl_unit                        []
% 19.64/3.02  --share_sel_clauses                     true
% 19.64/3.02  --reset_solvers                         false
% 19.64/3.02  --bc_imp_inh                            [conj_cone]
% 19.64/3.02  --conj_cone_tolerance                   3.
% 19.64/3.02  --extra_neg_conj                        none
% 19.64/3.02  --large_theory_mode                     true
% 19.64/3.02  --prolific_symb_bound                   200
% 19.64/3.02  --lt_threshold                          2000
% 19.64/3.02  --clause_weak_htbl                      true
% 19.64/3.02  --gc_record_bc_elim                     false
% 19.64/3.02  
% 19.64/3.02  ------ Preprocessing Options
% 19.64/3.02  
% 19.64/3.02  --preprocessing_flag                    true
% 19.64/3.02  --time_out_prep_mult                    0.1
% 19.64/3.02  --splitting_mode                        input
% 19.64/3.02  --splitting_grd                         true
% 19.64/3.02  --splitting_cvd                         false
% 19.64/3.02  --splitting_cvd_svl                     false
% 19.64/3.02  --splitting_nvd                         32
% 19.64/3.02  --sub_typing                            true
% 19.64/3.02  --prep_gs_sim                           true
% 19.64/3.02  --prep_unflatten                        true
% 19.64/3.02  --prep_res_sim                          true
% 19.64/3.02  --prep_upred                            true
% 19.64/3.02  --prep_sem_filter                       exhaustive
% 19.64/3.02  --prep_sem_filter_out                   false
% 19.64/3.02  --pred_elim                             true
% 19.64/3.02  --res_sim_input                         true
% 19.64/3.02  --eq_ax_congr_red                       true
% 19.64/3.02  --pure_diseq_elim                       true
% 19.64/3.02  --brand_transform                       false
% 19.64/3.02  --non_eq_to_eq                          false
% 19.64/3.02  --prep_def_merge                        true
% 19.64/3.02  --prep_def_merge_prop_impl              false
% 19.64/3.02  --prep_def_merge_mbd                    true
% 19.64/3.02  --prep_def_merge_tr_red                 false
% 19.64/3.02  --prep_def_merge_tr_cl                  false
% 19.64/3.02  --smt_preprocessing                     true
% 19.64/3.02  --smt_ac_axioms                         fast
% 19.64/3.02  --preprocessed_out                      false
% 19.64/3.02  --preprocessed_stats                    false
% 19.64/3.02  
% 19.64/3.02  ------ Abstraction refinement Options
% 19.64/3.02  
% 19.64/3.02  --abstr_ref                             []
% 19.64/3.02  --abstr_ref_prep                        false
% 19.64/3.02  --abstr_ref_until_sat                   false
% 19.64/3.02  --abstr_ref_sig_restrict                funpre
% 19.64/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.64/3.02  --abstr_ref_under                       []
% 19.64/3.02  
% 19.64/3.02  ------ SAT Options
% 19.64/3.02  
% 19.64/3.02  --sat_mode                              false
% 19.64/3.02  --sat_fm_restart_options                ""
% 19.64/3.02  --sat_gr_def                            false
% 19.64/3.02  --sat_epr_types                         true
% 19.64/3.02  --sat_non_cyclic_types                  false
% 19.64/3.02  --sat_finite_models                     false
% 19.64/3.02  --sat_fm_lemmas                         false
% 19.64/3.02  --sat_fm_prep                           false
% 19.64/3.02  --sat_fm_uc_incr                        true
% 19.64/3.02  --sat_out_model                         small
% 19.64/3.02  --sat_out_clauses                       false
% 19.64/3.02  
% 19.64/3.02  ------ QBF Options
% 19.64/3.02  
% 19.64/3.02  --qbf_mode                              false
% 19.64/3.02  --qbf_elim_univ                         false
% 19.64/3.02  --qbf_dom_inst                          none
% 19.64/3.02  --qbf_dom_pre_inst                      false
% 19.64/3.02  --qbf_sk_in                             false
% 19.64/3.02  --qbf_pred_elim                         true
% 19.64/3.02  --qbf_split                             512
% 19.64/3.02  
% 19.64/3.02  ------ BMC1 Options
% 19.64/3.02  
% 19.64/3.02  --bmc1_incremental                      false
% 19.64/3.02  --bmc1_axioms                           reachable_all
% 19.64/3.02  --bmc1_min_bound                        0
% 19.64/3.02  --bmc1_max_bound                        -1
% 19.64/3.02  --bmc1_max_bound_default                -1
% 19.64/3.02  --bmc1_symbol_reachability              true
% 19.64/3.02  --bmc1_property_lemmas                  false
% 19.64/3.02  --bmc1_k_induction                      false
% 19.64/3.02  --bmc1_non_equiv_states                 false
% 19.64/3.02  --bmc1_deadlock                         false
% 19.64/3.02  --bmc1_ucm                              false
% 19.64/3.02  --bmc1_add_unsat_core                   none
% 19.64/3.02  --bmc1_unsat_core_children              false
% 19.64/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.64/3.02  --bmc1_out_stat                         full
% 19.64/3.02  --bmc1_ground_init                      false
% 19.64/3.02  --bmc1_pre_inst_next_state              false
% 19.64/3.02  --bmc1_pre_inst_state                   false
% 19.64/3.02  --bmc1_pre_inst_reach_state             false
% 19.64/3.02  --bmc1_out_unsat_core                   false
% 19.64/3.02  --bmc1_aig_witness_out                  false
% 19.64/3.02  --bmc1_verbose                          false
% 19.64/3.02  --bmc1_dump_clauses_tptp                false
% 19.64/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.64/3.02  --bmc1_dump_file                        -
% 19.64/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.64/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.64/3.02  --bmc1_ucm_extend_mode                  1
% 19.64/3.02  --bmc1_ucm_init_mode                    2
% 19.64/3.02  --bmc1_ucm_cone_mode                    none
% 19.64/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.64/3.02  --bmc1_ucm_relax_model                  4
% 19.64/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.64/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.64/3.02  --bmc1_ucm_layered_model                none
% 19.64/3.02  --bmc1_ucm_max_lemma_size               10
% 19.64/3.02  
% 19.64/3.02  ------ AIG Options
% 19.64/3.02  
% 19.64/3.02  --aig_mode                              false
% 19.64/3.02  
% 19.64/3.02  ------ Instantiation Options
% 19.64/3.02  
% 19.64/3.02  --instantiation_flag                    true
% 19.64/3.02  --inst_sos_flag                         true
% 19.64/3.02  --inst_sos_phase                        true
% 19.64/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.64/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.64/3.02  --inst_lit_sel_side                     num_symb
% 19.64/3.02  --inst_solver_per_active                1400
% 19.64/3.02  --inst_solver_calls_frac                1.
% 19.64/3.02  --inst_passive_queue_type               priority_queues
% 19.64/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.64/3.02  --inst_passive_queues_freq              [25;2]
% 19.64/3.02  --inst_dismatching                      true
% 19.64/3.02  --inst_eager_unprocessed_to_passive     true
% 19.64/3.02  --inst_prop_sim_given                   true
% 19.64/3.02  --inst_prop_sim_new                     false
% 19.64/3.02  --inst_subs_new                         false
% 19.64/3.02  --inst_eq_res_simp                      false
% 19.64/3.02  --inst_subs_given                       false
% 19.64/3.02  --inst_orphan_elimination               true
% 19.64/3.02  --inst_learning_loop_flag               true
% 19.64/3.02  --inst_learning_start                   3000
% 19.64/3.02  --inst_learning_factor                  2
% 19.64/3.02  --inst_start_prop_sim_after_learn       3
% 19.64/3.02  --inst_sel_renew                        solver
% 19.64/3.02  --inst_lit_activity_flag                true
% 19.64/3.02  --inst_restr_to_given                   false
% 19.64/3.02  --inst_activity_threshold               500
% 19.64/3.02  --inst_out_proof                        true
% 19.64/3.02  
% 19.64/3.02  ------ Resolution Options
% 19.64/3.02  
% 19.64/3.02  --resolution_flag                       true
% 19.64/3.02  --res_lit_sel                           adaptive
% 19.64/3.02  --res_lit_sel_side                      none
% 19.64/3.02  --res_ordering                          kbo
% 19.64/3.02  --res_to_prop_solver                    active
% 19.64/3.02  --res_prop_simpl_new                    false
% 19.64/3.02  --res_prop_simpl_given                  true
% 19.64/3.02  --res_passive_queue_type                priority_queues
% 19.64/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.64/3.02  --res_passive_queues_freq               [15;5]
% 19.64/3.02  --res_forward_subs                      full
% 19.64/3.02  --res_backward_subs                     full
% 19.64/3.02  --res_forward_subs_resolution           true
% 19.64/3.02  --res_backward_subs_resolution          true
% 19.64/3.02  --res_orphan_elimination                true
% 19.64/3.02  --res_time_limit                        2.
% 19.64/3.02  --res_out_proof                         true
% 19.64/3.02  
% 19.64/3.02  ------ Superposition Options
% 19.64/3.02  
% 19.64/3.02  --superposition_flag                    true
% 19.64/3.02  --sup_passive_queue_type                priority_queues
% 19.64/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.64/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.64/3.02  --demod_completeness_check              fast
% 19.64/3.02  --demod_use_ground                      true
% 19.64/3.02  --sup_to_prop_solver                    passive
% 19.64/3.02  --sup_prop_simpl_new                    true
% 19.64/3.02  --sup_prop_simpl_given                  true
% 19.64/3.02  --sup_fun_splitting                     true
% 19.64/3.02  --sup_smt_interval                      50000
% 19.64/3.02  
% 19.64/3.02  ------ Superposition Simplification Setup
% 19.64/3.02  
% 19.64/3.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.64/3.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.64/3.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.64/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.64/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.64/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.64/3.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.64/3.02  --sup_immed_triv                        [TrivRules]
% 19.64/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_immed_bw_main                     []
% 19.64/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.64/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.64/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_input_bw                          []
% 19.64/3.02  
% 19.64/3.02  ------ Combination Options
% 19.64/3.02  
% 19.64/3.02  --comb_res_mult                         3
% 19.64/3.02  --comb_sup_mult                         2
% 19.64/3.02  --comb_inst_mult                        10
% 19.64/3.02  
% 19.64/3.02  ------ Debug Options
% 19.64/3.02  
% 19.64/3.02  --dbg_backtrace                         false
% 19.64/3.02  --dbg_dump_prop_clauses                 false
% 19.64/3.02  --dbg_dump_prop_clauses_file            -
% 19.64/3.02  --dbg_out_stat                          false
% 19.64/3.02  ------ Parsing...
% 19.64/3.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.64/3.02  
% 19.64/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 19.64/3.02  
% 19.64/3.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.64/3.02  
% 19.64/3.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.64/3.02  ------ Proving...
% 19.64/3.02  ------ Problem Properties 
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  clauses                                 31
% 19.64/3.02  conjectures                             8
% 19.64/3.02  EPR                                     3
% 19.64/3.02  Horn                                    22
% 19.64/3.02  unary                                   4
% 19.64/3.02  binary                                  5
% 19.64/3.02  lits                                    97
% 19.64/3.02  lits eq                                 8
% 19.64/3.02  fd_pure                                 0
% 19.64/3.02  fd_pseudo                               0
% 19.64/3.02  fd_cond                                 0
% 19.64/3.02  fd_pseudo_cond                          3
% 19.64/3.02  AC symbols                              0
% 19.64/3.02  
% 19.64/3.02  ------ Schedule dynamic 5 is on 
% 19.64/3.02  
% 19.64/3.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  ------ 
% 19.64/3.02  Current options:
% 19.64/3.02  ------ 
% 19.64/3.02  
% 19.64/3.02  ------ Input Options
% 19.64/3.02  
% 19.64/3.02  --out_options                           all
% 19.64/3.02  --tptp_safe_out                         true
% 19.64/3.02  --problem_path                          ""
% 19.64/3.02  --include_path                          ""
% 19.64/3.02  --clausifier                            res/vclausify_rel
% 19.64/3.02  --clausifier_options                    ""
% 19.64/3.02  --stdin                                 false
% 19.64/3.02  --stats_out                             all
% 19.64/3.02  
% 19.64/3.02  ------ General Options
% 19.64/3.02  
% 19.64/3.02  --fof                                   false
% 19.64/3.02  --time_out_real                         305.
% 19.64/3.02  --time_out_virtual                      -1.
% 19.64/3.02  --symbol_type_check                     false
% 19.64/3.02  --clausify_out                          false
% 19.64/3.02  --sig_cnt_out                           false
% 19.64/3.02  --trig_cnt_out                          false
% 19.64/3.02  --trig_cnt_out_tolerance                1.
% 19.64/3.02  --trig_cnt_out_sk_spl                   false
% 19.64/3.02  --abstr_cl_out                          false
% 19.64/3.02  
% 19.64/3.02  ------ Global Options
% 19.64/3.02  
% 19.64/3.02  --schedule                              default
% 19.64/3.02  --add_important_lit                     false
% 19.64/3.02  --prop_solver_per_cl                    1000
% 19.64/3.02  --min_unsat_core                        false
% 19.64/3.02  --soft_assumptions                      false
% 19.64/3.02  --soft_lemma_size                       3
% 19.64/3.02  --prop_impl_unit_size                   0
% 19.64/3.02  --prop_impl_unit                        []
% 19.64/3.02  --share_sel_clauses                     true
% 19.64/3.02  --reset_solvers                         false
% 19.64/3.02  --bc_imp_inh                            [conj_cone]
% 19.64/3.02  --conj_cone_tolerance                   3.
% 19.64/3.02  --extra_neg_conj                        none
% 19.64/3.02  --large_theory_mode                     true
% 19.64/3.02  --prolific_symb_bound                   200
% 19.64/3.02  --lt_threshold                          2000
% 19.64/3.02  --clause_weak_htbl                      true
% 19.64/3.02  --gc_record_bc_elim                     false
% 19.64/3.02  
% 19.64/3.02  ------ Preprocessing Options
% 19.64/3.02  
% 19.64/3.02  --preprocessing_flag                    true
% 19.64/3.02  --time_out_prep_mult                    0.1
% 19.64/3.02  --splitting_mode                        input
% 19.64/3.02  --splitting_grd                         true
% 19.64/3.02  --splitting_cvd                         false
% 19.64/3.02  --splitting_cvd_svl                     false
% 19.64/3.02  --splitting_nvd                         32
% 19.64/3.02  --sub_typing                            true
% 19.64/3.02  --prep_gs_sim                           true
% 19.64/3.02  --prep_unflatten                        true
% 19.64/3.02  --prep_res_sim                          true
% 19.64/3.02  --prep_upred                            true
% 19.64/3.02  --prep_sem_filter                       exhaustive
% 19.64/3.02  --prep_sem_filter_out                   false
% 19.64/3.02  --pred_elim                             true
% 19.64/3.02  --res_sim_input                         true
% 19.64/3.02  --eq_ax_congr_red                       true
% 19.64/3.02  --pure_diseq_elim                       true
% 19.64/3.02  --brand_transform                       false
% 19.64/3.02  --non_eq_to_eq                          false
% 19.64/3.02  --prep_def_merge                        true
% 19.64/3.02  --prep_def_merge_prop_impl              false
% 19.64/3.02  --prep_def_merge_mbd                    true
% 19.64/3.02  --prep_def_merge_tr_red                 false
% 19.64/3.02  --prep_def_merge_tr_cl                  false
% 19.64/3.02  --smt_preprocessing                     true
% 19.64/3.02  --smt_ac_axioms                         fast
% 19.64/3.02  --preprocessed_out                      false
% 19.64/3.02  --preprocessed_stats                    false
% 19.64/3.02  
% 19.64/3.02  ------ Abstraction refinement Options
% 19.64/3.02  
% 19.64/3.02  --abstr_ref                             []
% 19.64/3.02  --abstr_ref_prep                        false
% 19.64/3.02  --abstr_ref_until_sat                   false
% 19.64/3.02  --abstr_ref_sig_restrict                funpre
% 19.64/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.64/3.02  --abstr_ref_under                       []
% 19.64/3.02  
% 19.64/3.02  ------ SAT Options
% 19.64/3.02  
% 19.64/3.02  --sat_mode                              false
% 19.64/3.02  --sat_fm_restart_options                ""
% 19.64/3.02  --sat_gr_def                            false
% 19.64/3.02  --sat_epr_types                         true
% 19.64/3.02  --sat_non_cyclic_types                  false
% 19.64/3.02  --sat_finite_models                     false
% 19.64/3.02  --sat_fm_lemmas                         false
% 19.64/3.02  --sat_fm_prep                           false
% 19.64/3.02  --sat_fm_uc_incr                        true
% 19.64/3.02  --sat_out_model                         small
% 19.64/3.02  --sat_out_clauses                       false
% 19.64/3.02  
% 19.64/3.02  ------ QBF Options
% 19.64/3.02  
% 19.64/3.02  --qbf_mode                              false
% 19.64/3.02  --qbf_elim_univ                         false
% 19.64/3.02  --qbf_dom_inst                          none
% 19.64/3.02  --qbf_dom_pre_inst                      false
% 19.64/3.02  --qbf_sk_in                             false
% 19.64/3.02  --qbf_pred_elim                         true
% 19.64/3.02  --qbf_split                             512
% 19.64/3.02  
% 19.64/3.02  ------ BMC1 Options
% 19.64/3.02  
% 19.64/3.02  --bmc1_incremental                      false
% 19.64/3.02  --bmc1_axioms                           reachable_all
% 19.64/3.02  --bmc1_min_bound                        0
% 19.64/3.02  --bmc1_max_bound                        -1
% 19.64/3.02  --bmc1_max_bound_default                -1
% 19.64/3.02  --bmc1_symbol_reachability              true
% 19.64/3.02  --bmc1_property_lemmas                  false
% 19.64/3.02  --bmc1_k_induction                      false
% 19.64/3.02  --bmc1_non_equiv_states                 false
% 19.64/3.02  --bmc1_deadlock                         false
% 19.64/3.02  --bmc1_ucm                              false
% 19.64/3.02  --bmc1_add_unsat_core                   none
% 19.64/3.02  --bmc1_unsat_core_children              false
% 19.64/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.64/3.02  --bmc1_out_stat                         full
% 19.64/3.02  --bmc1_ground_init                      false
% 19.64/3.02  --bmc1_pre_inst_next_state              false
% 19.64/3.02  --bmc1_pre_inst_state                   false
% 19.64/3.02  --bmc1_pre_inst_reach_state             false
% 19.64/3.02  --bmc1_out_unsat_core                   false
% 19.64/3.02  --bmc1_aig_witness_out                  false
% 19.64/3.02  --bmc1_verbose                          false
% 19.64/3.02  --bmc1_dump_clauses_tptp                false
% 19.64/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.64/3.02  --bmc1_dump_file                        -
% 19.64/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.64/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.64/3.02  --bmc1_ucm_extend_mode                  1
% 19.64/3.02  --bmc1_ucm_init_mode                    2
% 19.64/3.02  --bmc1_ucm_cone_mode                    none
% 19.64/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.64/3.02  --bmc1_ucm_relax_model                  4
% 19.64/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.64/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.64/3.02  --bmc1_ucm_layered_model                none
% 19.64/3.02  --bmc1_ucm_max_lemma_size               10
% 19.64/3.02  
% 19.64/3.02  ------ AIG Options
% 19.64/3.02  
% 19.64/3.02  --aig_mode                              false
% 19.64/3.02  
% 19.64/3.02  ------ Instantiation Options
% 19.64/3.02  
% 19.64/3.02  --instantiation_flag                    true
% 19.64/3.02  --inst_sos_flag                         true
% 19.64/3.02  --inst_sos_phase                        true
% 19.64/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.64/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.64/3.02  --inst_lit_sel_side                     none
% 19.64/3.02  --inst_solver_per_active                1400
% 19.64/3.02  --inst_solver_calls_frac                1.
% 19.64/3.02  --inst_passive_queue_type               priority_queues
% 19.64/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.64/3.02  --inst_passive_queues_freq              [25;2]
% 19.64/3.02  --inst_dismatching                      true
% 19.64/3.02  --inst_eager_unprocessed_to_passive     true
% 19.64/3.02  --inst_prop_sim_given                   true
% 19.64/3.02  --inst_prop_sim_new                     false
% 19.64/3.02  --inst_subs_new                         false
% 19.64/3.02  --inst_eq_res_simp                      false
% 19.64/3.02  --inst_subs_given                       false
% 19.64/3.02  --inst_orphan_elimination               true
% 19.64/3.02  --inst_learning_loop_flag               true
% 19.64/3.02  --inst_learning_start                   3000
% 19.64/3.02  --inst_learning_factor                  2
% 19.64/3.02  --inst_start_prop_sim_after_learn       3
% 19.64/3.02  --inst_sel_renew                        solver
% 19.64/3.02  --inst_lit_activity_flag                true
% 19.64/3.02  --inst_restr_to_given                   false
% 19.64/3.02  --inst_activity_threshold               500
% 19.64/3.02  --inst_out_proof                        true
% 19.64/3.02  
% 19.64/3.02  ------ Resolution Options
% 19.64/3.02  
% 19.64/3.02  --resolution_flag                       false
% 19.64/3.02  --res_lit_sel                           adaptive
% 19.64/3.02  --res_lit_sel_side                      none
% 19.64/3.02  --res_ordering                          kbo
% 19.64/3.02  --res_to_prop_solver                    active
% 19.64/3.02  --res_prop_simpl_new                    false
% 19.64/3.02  --res_prop_simpl_given                  true
% 19.64/3.02  --res_passive_queue_type                priority_queues
% 19.64/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.64/3.02  --res_passive_queues_freq               [15;5]
% 19.64/3.02  --res_forward_subs                      full
% 19.64/3.02  --res_backward_subs                     full
% 19.64/3.02  --res_forward_subs_resolution           true
% 19.64/3.02  --res_backward_subs_resolution          true
% 19.64/3.02  --res_orphan_elimination                true
% 19.64/3.02  --res_time_limit                        2.
% 19.64/3.02  --res_out_proof                         true
% 19.64/3.02  
% 19.64/3.02  ------ Superposition Options
% 19.64/3.02  
% 19.64/3.02  --superposition_flag                    true
% 19.64/3.02  --sup_passive_queue_type                priority_queues
% 19.64/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.64/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.64/3.02  --demod_completeness_check              fast
% 19.64/3.02  --demod_use_ground                      true
% 19.64/3.02  --sup_to_prop_solver                    passive
% 19.64/3.02  --sup_prop_simpl_new                    true
% 19.64/3.02  --sup_prop_simpl_given                  true
% 19.64/3.02  --sup_fun_splitting                     true
% 19.64/3.02  --sup_smt_interval                      50000
% 19.64/3.02  
% 19.64/3.02  ------ Superposition Simplification Setup
% 19.64/3.02  
% 19.64/3.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.64/3.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.64/3.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.64/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.64/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.64/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.64/3.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.64/3.02  --sup_immed_triv                        [TrivRules]
% 19.64/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_immed_bw_main                     []
% 19.64/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.64/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.64/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.64/3.02  --sup_input_bw                          []
% 19.64/3.02  
% 19.64/3.02  ------ Combination Options
% 19.64/3.02  
% 19.64/3.02  --comb_res_mult                         3
% 19.64/3.02  --comb_sup_mult                         2
% 19.64/3.02  --comb_inst_mult                        10
% 19.64/3.02  
% 19.64/3.02  ------ Debug Options
% 19.64/3.02  
% 19.64/3.02  --dbg_backtrace                         false
% 19.64/3.02  --dbg_dump_prop_clauses                 false
% 19.64/3.02  --dbg_dump_prop_clauses_file            -
% 19.64/3.02  --dbg_out_stat                          false
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  ------ Proving...
% 19.64/3.02  
% 19.64/3.02  
% 19.64/3.02  % SZS status Theorem for theBenchmark.p
% 19.64/3.02  
% 19.64/3.02  % SZS output start CNFRefutation for theBenchmark.p
% 19.64/3.02  
% 19.64/3.02  fof(f9,axiom,(
% 19.64/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f25,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(ennf_transformation,[],[f9])).
% 19.64/3.02  
% 19.64/3.02  fof(f26,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(flattening,[],[f25])).
% 19.64/3.02  
% 19.64/3.02  fof(f36,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(nnf_transformation,[],[f26])).
% 19.64/3.02  
% 19.64/3.02  fof(f37,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(flattening,[],[f36])).
% 19.64/3.02  
% 19.64/3.02  fof(f38,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(rectify,[],[f37])).
% 19.64/3.02  
% 19.64/3.02  fof(f39,plain,(
% 19.64/3.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f40,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 19.64/3.02  
% 19.64/3.02  fof(f63,plain,(
% 19.64/3.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f40])).
% 19.64/3.02  
% 19.64/3.02  fof(f87,plain,(
% 19.64/3.02    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(equality_resolution,[],[f63])).
% 19.64/3.02  
% 19.64/3.02  fof(f12,conjecture,(
% 19.64/3.02    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f13,negated_conjecture,(
% 19.64/3.02    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 19.64/3.02    inference(negated_conjecture,[],[f12])).
% 19.64/3.02  
% 19.64/3.02  fof(f14,plain,(
% 19.64/3.02    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 19.64/3.02    inference(rectify,[],[f13])).
% 19.64/3.02  
% 19.64/3.02  fof(f16,plain,(
% 19.64/3.02    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 19.64/3.02    inference(pure_predicate_removal,[],[f14])).
% 19.64/3.02  
% 19.64/3.02  fof(f29,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 19.64/3.02    inference(ennf_transformation,[],[f16])).
% 19.64/3.02  
% 19.64/3.02  fof(f30,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.64/3.02    inference(flattening,[],[f29])).
% 19.64/3.02  
% 19.64/3.02  fof(f41,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.64/3.02    inference(nnf_transformation,[],[f30])).
% 19.64/3.02  
% 19.64/3.02  fof(f42,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.64/3.02    inference(flattening,[],[f41])).
% 19.64/3.02  
% 19.64/3.02  fof(f43,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.64/3.02    inference(rectify,[],[f42])).
% 19.64/3.02  
% 19.64/3.02  fof(f48,plain,(
% 19.64/3.02    ( ! [X0,X1] : (! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k2_yellow_0(X0,sK6(X5)) = X5 & r2_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f47,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r1_lattice3(X0,X2,sK5) | ~r1_lattice3(X0,X1,sK5)) & (r1_lattice3(X0,X2,sK5) | r1_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f46,plain,(
% 19.64/3.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r1_lattice3(X0,sK4,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,sK4,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f45,plain,(
% 19.64/3.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,sK3,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f44,plain,(
% 19.64/3.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK2,X2,X3) | ~r1_lattice3(sK2,X1,X3)) & (r1_lattice3(sK2,X2,X3) | r1_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK2,X6) = X5 & r2_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f49,plain,(
% 19.64/3.02    ((((~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)) & (r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK2,sK6(X5)) = X5 & r2_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 19.64/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f43,f48,f47,f46,f45,f44])).
% 19.64/3.02  
% 19.64/3.02  fof(f75,plain,(
% 19.64/3.02    l1_orders_2(sK2)),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f8,axiom,(
% 19.64/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f23,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(ennf_transformation,[],[f8])).
% 19.64/3.02  
% 19.64/3.02  fof(f24,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(flattening,[],[f23])).
% 19.64/3.02  
% 19.64/3.02  fof(f32,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(nnf_transformation,[],[f24])).
% 19.64/3.02  
% 19.64/3.02  fof(f33,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(rectify,[],[f32])).
% 19.64/3.02  
% 19.64/3.02  fof(f34,plain,(
% 19.64/3.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 19.64/3.02    introduced(choice_axiom,[])).
% 19.64/3.02  
% 19.64/3.02  fof(f35,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 19.64/3.02  
% 19.64/3.02  fof(f60,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f35])).
% 19.64/3.02  
% 19.64/3.02  fof(f59,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f35])).
% 19.64/3.02  
% 19.64/3.02  fof(f3,axiom,(
% 19.64/3.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f17,plain,(
% 19.64/3.02    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 19.64/3.02    inference(ennf_transformation,[],[f3])).
% 19.64/3.02  
% 19.64/3.02  fof(f52,plain,(
% 19.64/3.02    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f17])).
% 19.64/3.02  
% 19.64/3.02  fof(f85,plain,(
% 19.64/3.02    r1_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK3,sK5)),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f84,plain,(
% 19.64/3.02    m1_subset_1(sK5,u1_struct_0(sK2))),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f4,axiom,(
% 19.64/3.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f15,plain,(
% 19.64/3.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 19.64/3.02    inference(unused_predicate_definition_removal,[],[f4])).
% 19.64/3.02  
% 19.64/3.02  fof(f18,plain,(
% 19.64/3.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 19.64/3.02    inference(ennf_transformation,[],[f15])).
% 19.64/3.02  
% 19.64/3.02  fof(f53,plain,(
% 19.64/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f18])).
% 19.64/3.02  
% 19.64/3.02  fof(f11,axiom,(
% 19.64/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f28,plain,(
% 19.64/3.02    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(ennf_transformation,[],[f11])).
% 19.64/3.02  
% 19.64/3.02  fof(f71,plain,(
% 19.64/3.02    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f28])).
% 19.64/3.02  
% 19.64/3.02  fof(f10,axiom,(
% 19.64/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f27,plain,(
% 19.64/3.02    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.64/3.02    inference(ennf_transformation,[],[f10])).
% 19.64/3.02  
% 19.64/3.02  fof(f67,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f27])).
% 19.64/3.02  
% 19.64/3.02  fof(f86,plain,(
% 19.64/3.02    ~r1_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK2,sK3,sK5)),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f61,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f35])).
% 19.64/3.02  
% 19.64/3.02  fof(f58,plain,(
% 19.64/3.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f35])).
% 19.64/3.02  
% 19.64/3.02  fof(f7,axiom,(
% 19.64/3.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f21,plain,(
% 19.64/3.02    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.64/3.02    inference(ennf_transformation,[],[f7])).
% 19.64/3.02  
% 19.64/3.02  fof(f22,plain,(
% 19.64/3.02    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.64/3.02    inference(flattening,[],[f21])).
% 19.64/3.02  
% 19.64/3.02  fof(f57,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f22])).
% 19.64/3.02  
% 19.64/3.02  fof(f74,plain,(
% 19.64/3.02    v3_orders_2(sK2)),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f73,plain,(
% 19.64/3.02    ~v2_struct_0(sK2)),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f6,axiom,(
% 19.64/3.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f19,plain,(
% 19.64/3.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.64/3.02    inference(ennf_transformation,[],[f6])).
% 19.64/3.02  
% 19.64/3.02  fof(f20,plain,(
% 19.64/3.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.64/3.02    inference(flattening,[],[f19])).
% 19.64/3.02  
% 19.64/3.02  fof(f31,plain,(
% 19.64/3.02    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.64/3.02    inference(nnf_transformation,[],[f20])).
% 19.64/3.02  
% 19.64/3.02  fof(f55,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f31])).
% 19.64/3.02  
% 19.64/3.02  fof(f5,axiom,(
% 19.64/3.02    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f54,plain,(
% 19.64/3.02    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f5])).
% 19.64/3.02  
% 19.64/3.02  fof(f83,plain,(
% 19.64/3.02    ( ! [X4] : (r2_hidden(k2_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f78,plain,(
% 19.64/3.02    ( ! [X7] : (r2_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f68,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f27])).
% 19.64/3.02  
% 19.64/3.02  fof(f65,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | r1_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f40])).
% 19.64/3.02  
% 19.64/3.02  fof(f64,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f40])).
% 19.64/3.02  
% 19.64/3.02  fof(f66,plain,(
% 19.64/3.02    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.64/3.02    inference(cnf_transformation,[],[f40])).
% 19.64/3.02  
% 19.64/3.02  fof(f1,axiom,(
% 19.64/3.02    v1_xboole_0(k1_xboole_0)),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f50,plain,(
% 19.64/3.02    v1_xboole_0(k1_xboole_0)),
% 19.64/3.02    inference(cnf_transformation,[],[f1])).
% 19.64/3.02  
% 19.64/3.02  fof(f2,axiom,(
% 19.64/3.02    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 19.64/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.64/3.02  
% 19.64/3.02  fof(f51,plain,(
% 19.64/3.02    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f2])).
% 19.64/3.02  
% 19.64/3.02  fof(f82,plain,(
% 19.64/3.02    ( ! [X5] : (k2_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f81,plain,(
% 19.64/3.02    ( ! [X5] : (r2_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  fof(f80,plain,(
% 19.64/3.02    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 19.64/3.02    inference(cnf_transformation,[],[f49])).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2780,plain,
% 19.64/3.02      ( ~ r1_orders_2(X0_53,X0_54,X1_54)
% 19.64/3.02      | r1_orders_2(X0_53,X2_54,X3_54)
% 19.64/3.02      | X2_54 != X0_54
% 19.64/3.02      | X3_54 != X1_54 ),
% 19.64/3.02      theory(equality) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_29402,plain,
% 19.64/3.02      ( ~ r1_orders_2(sK2,X0_54,X1_54)
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 19.64/3.02      | sK0(sK2,sK4,sK5) != X1_54
% 19.64/3.02      | sK5 != X0_54 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2780]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_29658,plain,
% 19.64/3.02      ( ~ r1_orders_2(sK2,sK5,X0_54)
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 19.64/3.02      | sK0(sK2,sK4,sK5) != X0_54
% 19.64/3.02      | sK5 != sK5 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_29402]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_30304,plain,
% 19.64/3.02      ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 19.64/3.02      | ~ r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 19.64/3.02      | sK0(sK2,sK4,sK5) != k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 19.64/3.02      | sK5 != sK5 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_29658]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_15,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f87]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_34,negated_conjecture,
% 19.64/3.02      ( l1_orders_2(sK2) ),
% 19.64/3.02      inference(cnf_transformation,[],[f75]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_821,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_822,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_821]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2749,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | r1_orders_2(sK2,X1_54,k2_yellow_0(sK2,X0_54))
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(sK2,X0_54),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_822]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_29473,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),X0_54)
% 19.64/3.02      | r1_orders_2(sK2,X0_54,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 19.64/3.02      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2749]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_29869,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 19.64/3.02      | r1_orders_2(sK2,sK5,k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))))
% 19.64/3.02      | ~ r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 19.64/3.02      | ~ m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_29473]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2775,plain,( X0_54 = X0_54 ),theory(equality) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_28079,plain,
% 19.64/3.02      ( sK0(sK2,X0_54,sK5) = sK0(sK2,X0_54,sK5) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_28080,plain,
% 19.64/3.02      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_28079]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2778,plain,
% 19.64/3.02      ( ~ m1_subset_1(X0_54,X1_54)
% 19.64/3.02      | m1_subset_1(X2_54,X3_54)
% 19.64/3.02      | X2_54 != X0_54
% 19.64/3.02      | X3_54 != X1_54 ),
% 19.64/3.02      theory(equality) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3609,plain,
% 19.64/3.02      ( ~ m1_subset_1(X0_54,X1_54)
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2))
% 19.64/3.02      | X2_54 != X0_54
% 19.64/3.02      | u1_struct_0(sK2) != X1_54 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2778]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3823,plain,
% 19.64/3.02      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | X1_54 != X0_54
% 19.64/3.02      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3609]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_18440,plain,
% 19.64/3.02      ( m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2))
% 19.64/3.02      | X0_54 != sK0(sK2,X1_54,sK5)
% 19.64/3.02      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3823]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_27767,plain,
% 19.64/3.02      ( ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))),u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,sK6(sK0(sK2,X1_54,sK5))) != sK0(sK2,X0_54,sK5)
% 19.64/3.02      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_18440]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_27769,plain,
% 19.64/3.02      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 19.64/3.02      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_27767]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_9,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r2_hidden(sK0(X0,X1,X2),X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f60]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_941,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r2_hidden(sK0(X0,X1,X2),X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_942,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | r2_hidden(sK0(sK2,X0,X1),X0)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_941]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2743,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_942]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3517,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
% 19.64/3.02      | r2_hidden(sK0(sK2,X0_54,X1_54),X0_54) = iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_10,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f59]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_926,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_10,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_927,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_926]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2744,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_927]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3516,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,X0_54,X1_54),u1_struct_0(sK2)) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2744]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2,plain,
% 19.64/3.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 19.64/3.02      inference(cnf_transformation,[],[f52]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2770,plain,
% 19.64/3.02      ( ~ r2_hidden(X0_54,X1_54)
% 19.64/3.02      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_2]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3489,plain,
% 19.64/3.02      ( r2_hidden(X0_54,X1_54) != iProver_top
% 19.64/3.02      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(X1_54)) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_24,negated_conjecture,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 19.64/3.02      inference(cnf_transformation,[],[f85]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2768,negated_conjecture,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_24]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3491,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_25,negated_conjecture,
% 19.64/3.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(cnf_transformation,[],[f84]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2767,negated_conjecture,
% 19.64/3.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_25]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3492,plain,
% 19.64/3.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2767]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3,plain,
% 19.64/3.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.64/3.02      inference(cnf_transformation,[],[f53]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_22,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X3,X2)
% 19.64/3.02      | ~ r1_tarski(X3,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f71]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_482,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X3,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.64/3.02      | ~ l1_orders_2(X0)
% 19.64/3.02      | X3 != X4
% 19.64/3.02      | X1 != X5 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_483,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X3,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_482]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_720,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X3,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_483,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_721,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | r1_lattice3(sK2,X2,X1)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_720]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2755,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | r1_lattice3(sK2,X2_54,X1_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_721]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3505,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54) != iProver_top
% 19.64/3.02      | r1_lattice3(sK2,X2_54,X1_54) = iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2755]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4153,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
% 19.64/3.02      | r1_lattice3(sK2,X1_54,sK5) = iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3492,c_3505]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4156,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,k1_zfmisc_1(sK3)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3491,c_4153]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4229,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3489,c_4156]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4237,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X1_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(X1_54))) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_4229,c_4153]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_5639,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,k1_tarski(X1_54)) != iProver_top
% 19.64/3.02      | r2_hidden(X1_54,sK3) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3489,c_4237]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_5666,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3517,c_5639]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6664,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X1_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)))) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_5666,c_4153]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_7237,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54))) != iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3489,c_6664]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_7279,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3517,c_7237]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_9607,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X1_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)))) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_7279,c_4153]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_10951,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54))) != iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3489,c_9607]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_11541,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3517,c_10951]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_12912,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X1_54),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X1_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X1_54),X2_54)),X3_54)),X4_54)))) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_11541,c_4153]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_13645,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(X2_54),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X2_54,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X3_54)),X4_54))) != iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3489,c_12912]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_13992,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)),sK5) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_3517,c_13645]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_20,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 19.64/3.02      | r1_orders_2(X0,X2,X1)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f67]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_736,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 19.64/3.02      | r1_orders_2(X0,X2,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_737,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
% 19.64/3.02      | r1_orders_2(sK2,X1,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_736]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2754,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 19.64/3.02      | r1_orders_2(sK2,X1_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_737]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3506,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) != iProver_top
% 19.64/3.02      | r1_orders_2(sK2,X1_54,X0_54) = iProver_top
% 19.64/3.02      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_2754]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_15864,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
% 19.64/3.02      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(superposition,[status(thm)],[c_13992,c_3506]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_60,plain,
% 19.64/3.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_23,negated_conjecture,
% 19.64/3.02      ( ~ r1_lattice3(sK2,sK3,sK5) | ~ r1_lattice3(sK2,sK4,sK5) ),
% 19.64/3.02      inference(cnf_transformation,[],[f86]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_62,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) != iProver_top
% 19.64/3.02      | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2794,plain,
% 19.64/3.02      ( sK4 = sK4 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_8,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f61]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_956,plain,
% 19.64/3.02      ( r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_957,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_956]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2742,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | ~ r1_orders_2(sK2,X1_54,sK0(sK2,X0_54,X1_54))
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_957]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3614,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.02      | ~ r1_orders_2(sK2,sK5,sK0(sK2,X0_54,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2742]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3731,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5)
% 19.64/3.02      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3614]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3732,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3731]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3620,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.02      | r2_hidden(sK0(sK2,X0_54,sK5),X0_54)
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2743]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3757,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5)
% 19.64/3.02      | r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3620]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3758,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 19.64/3.02      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3757]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3604,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.02      | m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2744]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3770,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5)
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3604]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3771,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3770]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3586,plain,
% 19.64/3.02      ( ~ r2_hidden(X0_54,sK3)
% 19.64/3.02      | m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2770]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3868,plain,
% 19.64/3.02      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 19.64/3.02      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3586]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3869,plain,
% 19.64/3.02      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 19.64/3.02      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3868]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_11,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_orders_2(X0,X2,X3)
% 19.64/3.02      | ~ r2_hidden(X3,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f58]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_905,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_orders_2(X0,X2,X3)
% 19.64/3.02      | ~ r2_hidden(X3,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_11,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_906,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | r1_orders_2(sK2,X1,X2)
% 19.64/3.02      | ~ r2_hidden(X2,X0)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_905]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2745,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | r1_orders_2(sK2,X1_54,X2_54)
% 19.64/3.02      | ~ r2_hidden(X2_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X2_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_906]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3661,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.02      | r1_orders_2(sK2,sK5,X1_54)
% 19.64/3.02      | ~ r2_hidden(X1_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2745]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3871,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_54)
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3661]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3882,plain,
% 19.64/3.02      ( r1_lattice3(sK2,X0_54,sK5) != iProver_top
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
% 19.64/3.02      | r2_hidden(sK0(sK2,sK3,sK5),X0_54) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3871]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3884,plain,
% 19.64/3.02      ( r1_lattice3(sK2,sK4,sK5) != iProver_top
% 19.64/3.02      | r1_orders_2(sK2,sK5,sK0(sK2,sK3,sK5)) = iProver_top
% 19.64/3.02      | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3882]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_7,plain,
% 19.64/3.02      ( r3_orders_2(X0,X1,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | v2_struct_0(X0)
% 19.64/3.02      | ~ v3_orders_2(X0)
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f57]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_35,negated_conjecture,
% 19.64/3.02      ( v3_orders_2(sK2) ),
% 19.64/3.02      inference(cnf_transformation,[],[f74]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_601,plain,
% 19.64/3.02      ( r3_orders_2(X0,X1,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | v2_struct_0(X0)
% 19.64/3.02      | ~ l1_orders_2(X0)
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_7,c_35]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_602,plain,
% 19.64/3.02      ( r3_orders_2(sK2,X0,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | v2_struct_0(sK2)
% 19.64/3.02      | ~ l1_orders_2(sK2) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_601]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_36,negated_conjecture,
% 19.64/3.02      ( ~ v2_struct_0(sK2) ),
% 19.64/3.02      inference(cnf_transformation,[],[f73]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_606,plain,
% 19.64/3.02      ( r3_orders_2(sK2,X0,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(global_propositional_subsumption,
% 19.64/3.02                [status(thm)],
% 19.64/3.02                [c_602,c_36,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6,plain,
% 19.64/3.02      ( r1_orders_2(X0,X1,X2)
% 19.64/3.02      | ~ r3_orders_2(X0,X1,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | v2_struct_0(X0)
% 19.64/3.02      | ~ v3_orders_2(X0)
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f55]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_622,plain,
% 19.64/3.02      ( r1_orders_2(X0,X1,X2)
% 19.64/3.02      | ~ r3_orders_2(X0,X1,X2)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | v2_struct_0(X0)
% 19.64/3.02      | ~ l1_orders_2(X0)
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_6,c_35]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_623,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0,X1)
% 19.64/3.02      | ~ r3_orders_2(sK2,X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | v2_struct_0(sK2)
% 19.64/3.02      | ~ l1_orders_2(sK2) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_622]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_627,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0,X1)
% 19.64/3.02      | ~ r3_orders_2(sK2,X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(global_propositional_subsumption,
% 19.64/3.02                [status(thm)],
% 19.64/3.02                [c_623,c_36,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_685,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | X0 != X2
% 19.64/3.02      | X1 != X2
% 19.64/3.02      | sK2 != sK2 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_606,c_627]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_686,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_685]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2757,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_686]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2772,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ sP1_iProver_split ),
% 19.64/3.02      inference(splitting,
% 19.64/3.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 19.64/3.02                [c_2757]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2773,plain,
% 19.64/3.02      ( sP1_iProver_split | sP0_iProver_split ),
% 19.64/3.02      inference(splitting,
% 19.64/3.02                [splitting(split),new_symbols(definition,[])],
% 19.64/3.02                [c_2757]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2771,plain,
% 19.64/3.02      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 19.64/3.02      inference(splitting,
% 19.64/3.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 19.64/3.02                [c_2757]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2926,plain,
% 19.64/3.02      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | r1_orders_2(sK2,X0_54,X0_54) ),
% 19.64/3.02      inference(global_propositional_subsumption,
% 19.64/3.02                [status(thm)],
% 19.64/3.02                [c_2772,c_2773,c_2771]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2927,plain,
% 19.64/3.02      ( r1_orders_2(sK2,X0_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(renaming,[status(thm)],[c_2926]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3720,plain,
% 19.64/3.02      ( r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK0(sK2,X0_54,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2927]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3918,plain,
% 19.64/3.02      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3720]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3919,plain,
% 19.64/3.02      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) = iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_3918]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4,plain,
% 19.64/3.02      ( v1_finset_1(k1_tarski(X0)) ),
% 19.64/3.02      inference(cnf_transformation,[],[f54]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_26,negated_conjecture,
% 19.64/3.02      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 19.64/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 19.64/3.02      | ~ v1_finset_1(X0)
% 19.64/3.02      | k1_xboole_0 = X0 ),
% 19.64/3.02      inference(cnf_transformation,[],[f83]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_547,plain,
% 19.64/3.02      ( r2_hidden(k2_yellow_0(sK2,X0),sK4)
% 19.64/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_tarski(X1) != X0
% 19.64/3.02      | k1_xboole_0 = X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_548,plain,
% 19.64/3.02      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0)),sK4)
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(X0) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_547]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2759,plain,
% 19.64/3.02      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(X0_54)),sK4)
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(X0_54) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_548]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4120,plain,
% 19.64/3.02      ( r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2759]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4121,plain,
% 19.64/3.02      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 19.64/3.02      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
% 19.64/3.02      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_4120]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_31,negated_conjecture,
% 19.64/3.02      ( r2_yellow_0(sK2,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 19.64/3.02      | ~ v1_finset_1(X0)
% 19.64/3.02      | k1_xboole_0 = X0 ),
% 19.64/3.02      inference(cnf_transformation,[],[f78]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_532,plain,
% 19.64/3.02      ( r2_yellow_0(sK2,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_tarski(X1) != X0
% 19.64/3.02      | k1_xboole_0 = X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_4,c_31]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_533,plain,
% 19.64/3.02      ( r2_yellow_0(sK2,k1_tarski(X0))
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(X0) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_532]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2760,plain,
% 19.64/3.02      ( r2_yellow_0(sK2,k1_tarski(X0_54))
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(X0_54),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(X0_54) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_533]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4119,plain,
% 19.64/3.02      ( r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.02      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 19.64/3.02      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2760]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4123,plain,
% 19.64/3.02      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 19.64/3.02      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 19.64/3.02      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_4119]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_19,plain,
% 19.64/3.02      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 19.64/3.02      | ~ r1_orders_2(X0,X2,X1)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0) ),
% 19.64/3.02      inference(cnf_transformation,[],[f68]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_754,plain,
% 19.64/3.02      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 19.64/3.02      | ~ r1_orders_2(X0,X2,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_755,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0),X1)
% 19.64/3.02      | ~ r1_orders_2(sK2,X1,X0)
% 19.64/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_754]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2753,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54)
% 19.64/3.02      | ~ r1_orders_2(sK2,X1_54,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_755]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3678,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(X0_54),sK0(sK2,X1_54,sK5))
% 19.64/3.02      | ~ r1_orders_2(sK2,sK0(sK2,X1_54,sK5),X0_54)
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,X1_54,sK5),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2753]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_3893,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_54,sK5))
% 19.64/3.02      | ~ r1_orders_2(sK2,sK0(sK2,X0_54,sK5),sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,X0_54,sK5),u1_struct_0(sK2))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3678]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4168,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_3893]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_4169,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
% 19.64/3.02      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_4168]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6237,plain,
% 19.64/3.02      ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6659,plain,
% 19.64/3.02      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_13,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X1,sK1(X0,X1,X2))
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0)
% 19.64/3.02      | k2_yellow_0(X0,X1) = X2 ),
% 19.64/3.02      inference(cnf_transformation,[],[f65]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_863,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | r1_lattice3(X0,X1,sK1(X0,X1,X2))
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | k2_yellow_0(X0,X1) = X2
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_864,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | r1_lattice3(sK2,X0,sK1(sK2,X0,X1))
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,X0) = X1 ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_863]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2747,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | r1_lattice3(sK2,X0_54,sK1(sK2,X0_54,X1_54))
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,X0_54) = X1_54 ),
% 19.64/3.02      inference(subtyping,[status(esa)],[c_864]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6004,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54))
% 19.64/3.02      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_2747]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6772,plain,
% 19.64/3.02      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 19.64/3.02      | ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.02      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.02      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 19.64/3.02      inference(instantiation,[status(thm)],[c_6004]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_6773,plain,
% 19.64/3.02      ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
% 19.64/3.02      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.02      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 19.64/3.02      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.02      inference(predicate_to_equality,[status(thm)],[c_6772]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_14,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 19.64/3.02      | ~ l1_orders_2(X0)
% 19.64/3.02      | k2_yellow_0(X0,X1) = X2 ),
% 19.64/3.02      inference(cnf_transformation,[],[f64]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_842,plain,
% 19.64/3.02      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.02      | ~ r2_yellow_0(X0,X1)
% 19.64/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.02      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 19.64/3.02      | k2_yellow_0(X0,X1) = X2
% 19.64/3.02      | sK2 != X0 ),
% 19.64/3.02      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_843,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0)
% 19.64/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.02      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 19.64/3.02      | k2_yellow_0(sK2,X0) = X1 ),
% 19.64/3.02      inference(unflattening,[status(thm)],[c_842]) ).
% 19.64/3.02  
% 19.64/3.02  cnf(c_2748,plain,
% 19.64/3.02      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.02      | ~ r2_yellow_0(sK2,X0_54)
% 19.64/3.02      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.03      | m1_subset_1(sK1(sK2,X0_54,X1_54),u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,X0_54) = X1_54 ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_843]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6006,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 19.64/3.03      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.03      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2748]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6785,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.03      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 19.64/3.03      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_6006]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6786,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.03      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 19.64/3.03      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_6785]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_12,plain,
% 19.64/3.03      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.03      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 19.64/3.03      | ~ r2_yellow_0(X0,X1)
% 19.64/3.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.03      | ~ l1_orders_2(X0)
% 19.64/3.03      | k2_yellow_0(X0,X1) = X2 ),
% 19.64/3.03      inference(cnf_transformation,[],[f66]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_884,plain,
% 19.64/3.03      ( ~ r1_lattice3(X0,X1,X2)
% 19.64/3.03      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 19.64/3.03      | ~ r2_yellow_0(X0,X1)
% 19.64/3.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.64/3.03      | k2_yellow_0(X0,X1) = X2
% 19.64/3.03      | sK2 != X0 ),
% 19.64/3.03      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_885,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,X0,X1)
% 19.64/3.03      | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
% 19.64/3.03      | ~ r2_yellow_0(sK2,X0)
% 19.64/3.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,X0) = X1 ),
% 19.64/3.03      inference(unflattening,[status(thm)],[c_884]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2746,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,X0_54,X1_54)
% 19.64/3.03      | ~ r1_orders_2(sK2,sK1(sK2,X0_54,X1_54),X1_54)
% 19.64/3.03      | ~ r2_yellow_0(sK2,X0_54)
% 19.64/3.03      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,X0_54) = X1_54 ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_885]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6005,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54)
% 19.64/3.03      | ~ r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_54),X0_54)
% 19.64/3.03      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_54 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2746]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6800,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.03      | ~ r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.03      | ~ r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_6005]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6801,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 19.64/3.03      | r2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_6800]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2776,plain,
% 19.64/3.03      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 19.64/3.03      theory(equality) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4640,plain,
% 19.64/3.03      ( X0_54 != X1_54
% 19.64/3.03      | sK0(sK2,X2_54,sK5) != X1_54
% 19.64/3.03      | sK0(sK2,X2_54,sK5) = X0_54 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2776]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_5460,plain,
% 19.64/3.03      ( X0_54 != sK0(sK2,X1_54,sK5)
% 19.64/3.03      | sK0(sK2,X1_54,sK5) = X0_54
% 19.64/3.03      | sK0(sK2,X1_54,sK5) != sK0(sK2,X1_54,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_4640]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_7783,plain,
% 19.64/3.03      ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
% 19.64/3.03      | sK0(sK2,sK3,sK5) = k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_5460]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4999,plain,
% 19.64/3.03      ( X0_54 != X1_54
% 19.64/3.03      | k1_tarski(sK0(sK2,sK3,sK5)) != X1_54
% 19.64/3.03      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2776]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_7670,plain,
% 19.64/3.03      ( X0_54 != k1_tarski(sK0(sK2,sK3,sK5))
% 19.64/3.03      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_54
% 19.64/3.03      | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_4999]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_8519,plain,
% 19.64/3.03      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 19.64/3.03      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 19.64/3.03      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_7670]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2779,plain,
% 19.64/3.03      ( ~ r2_hidden(X0_54,X1_54)
% 19.64/3.03      | r2_hidden(X2_54,X3_54)
% 19.64/3.03      | X2_54 != X0_54
% 19.64/3.03      | X3_54 != X1_54 ),
% 19.64/3.03      theory(equality) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3581,plain,
% 19.64/3.03      ( ~ r2_hidden(X0_54,X1_54)
% 19.64/3.03      | r2_hidden(X2_54,sK4)
% 19.64/3.03      | X2_54 != X0_54
% 19.64/3.03      | sK4 != X1_54 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2779]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6044,plain,
% 19.64/3.03      ( r2_hidden(X0_54,sK4)
% 19.64/3.03      | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 19.64/3.03      | X0_54 != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | sK4 != sK4 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_3581]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_11459,plain,
% 19.64/3.03      ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
% 19.64/3.03      | ~ r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 19.64/3.03      | sK0(sK2,sK3,sK5) != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | sK4 != sK4 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_6044]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_11460,plain,
% 19.64/3.03      ( sK0(sK2,sK3,sK5) != k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 19.64/3.03      | sK4 != sK4
% 19.64/3.03      | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
% 19.64/3.03      | r2_hidden(k2_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_11459]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_0,plain,
% 19.64/3.03      ( v1_xboole_0(k1_xboole_0) ),
% 19.64/3.03      inference(cnf_transformation,[],[f50]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_1,plain,
% 19.64/3.03      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 19.64/3.03      inference(cnf_transformation,[],[f51]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_476,plain,
% 19.64/3.03      ( k1_tarski(X0) != k1_xboole_0 ),
% 19.64/3.03      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2761,plain,
% 19.64/3.03      ( k1_tarski(X0_54) != k1_xboole_0 ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_476]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_13834,plain,
% 19.64/3.03      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2761]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_10053,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(X0_54),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 19.64/3.03      | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),X0_54)
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.03      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2754]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_17015,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 19.64/3.03      | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 19.64/3.03      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 19.64/3.03      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_10053]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_17016,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
% 19.64/3.03      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_17015]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18329,plain,
% 19.64/3.03      ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_15864,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,
% 19.64/3.03                 c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,
% 19.64/3.03                 c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,c_17016]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18330,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_18329]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18335,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),X4_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X4_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_18330]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3518,plain,
% 19.64/3.03      ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,X1_54,sK0(sK2,X0_54,X1_54)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_2742]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18340,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18335,c_3518]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18497,plain,
% 19.64/3.03      ( m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18340,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18498,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_18497]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18504,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18498,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_12911,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_11541,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_15727,plain,
% 19.64/3.03      ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_12911,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_15728,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_15727]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_15733,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_15728]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18653,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),X3_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X3_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18504,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,
% 19.64/3.03                 c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,
% 19.64/3.03                 c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,c_15733,
% 19.64/3.03                 c_17016]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18659,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18653,c_3518]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18671,plain,
% 19.64/3.03      ( m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18659,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18672,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_18671]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18678,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18672,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_9606,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_7279,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_12775,plain,
% 19.64/3.03      ( m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_9606,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_12776,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_12775]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_12781,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_12776]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18703,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),X2_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X2_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18678,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,
% 19.64/3.03                 c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,
% 19.64/3.03                 c_6786,c_6801,c_7783,c_8519,c_11460,c_12781,c_13834,
% 19.64/3.03                 c_17016]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18709,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18703,c_3518]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18842,plain,
% 19.64/3.03      ( m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18709,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18843,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_54),X1_54)),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_18842]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18849,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18843,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_6663,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_5666,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_9110,plain,
% 19.64/3.03      ( m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_6663,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_9111,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK0(sK2,k1_tarski(X0_54),X1_54),u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_9110]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_9116,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_9111]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18878,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),X1_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,k1_tarski(X0_54),X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18849,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,
% 19.64/3.03                 c_3884,c_3919,c_4121,c_4123,c_4169,c_6237,c_6659,c_6773,
% 19.64/3.03                 c_6786,c_6801,c_7783,c_8519,c_9116,c_11460,c_13834,
% 19.64/3.03                 c_17016]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18884,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18878,c_3518]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18898,plain,
% 19.64/3.03      ( r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18884,c_60,c_62,c_2794,c_3732,c_3758,c_3771,c_3869,
% 19.64/3.03                 c_3884,c_3919,c_4121,c_4123,c_4169,c_4229,c_6237,c_6659,
% 19.64/3.03                 c_6773,c_6786,c_6801,c_7783,c_8519,c_11460,c_13834,
% 19.64/3.03                 c_17016]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18899,plain,
% 19.64/3.03      ( r1_lattice3(sK2,k1_tarski(X0_54),sK5) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_18898]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18905,plain,
% 19.64/3.03      ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_18899,c_3506]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19089,plain,
% 19.64/3.03      ( m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,X0_54) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_18905,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19090,plain,
% 19.64/3.03      ( r1_orders_2(sK2,sK5,X0_54) = iProver_top
% 19.64/3.03      | r2_hidden(X0_54,sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_19089]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19096,plain,
% 19.64/3.03      ( r1_lattice3(sK2,X0_54,X1_54) = iProver_top
% 19.64/3.03      | r1_orders_2(sK2,sK5,sK0(sK2,X0_54,X1_54)) = iProver_top
% 19.64/3.03      | r2_hidden(sK0(sK2,X0_54,X1_54),sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_19090]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19246,plain,
% 19.64/3.03      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.03      | r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_19096,c_3518]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19261,plain,
% 19.64/3.03      ( r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top
% 19.64/3.03      | r1_lattice3(sK2,X0_54,sK5) = iProver_top ),
% 19.64/3.03      inference(global_propositional_subsumption,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_19246,c_60]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19262,plain,
% 19.64/3.03      ( r1_lattice3(sK2,X0_54,sK5) = iProver_top
% 19.64/3.03      | r2_hidden(sK0(sK2,X0_54,sK5),sK3) != iProver_top ),
% 19.64/3.03      inference(renaming,[status(thm)],[c_19261]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19265,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK3,sK5) = iProver_top
% 19.64/3.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3517,c_19262]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_19266,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK3,sK5) | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_19265]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3653,plain,
% 19.64/3.03      ( ~ r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.03      | r1_lattice3(sK2,X1_54,sK5)
% 19.64/3.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X0_54))
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2755]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4032,plain,
% 19.64/3.03      ( r1_lattice3(sK2,X0_54,sK5)
% 19.64/3.03      | ~ r1_lattice3(sK2,sK3,sK5)
% 19.64/3.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(sK3))
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_3653]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18536,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 19.64/3.03      | ~ r1_lattice3(sK2,sK3,sK5)
% 19.64/3.03      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_4032]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18298,plain,
% 19.64/3.03      ( sK0(sK2,X0_54,sK5) != sK0(sK2,X0_54,sK5)
% 19.64/3.03      | sK0(sK2,X0_54,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5)))
% 19.64/3.03      | k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,sK5))) != sK0(sK2,X0_54,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_5460]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_18310,plain,
% 19.64/3.03      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 19.64/3.03      | sK0(sK2,sK4,sK5) = k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 19.64/3.03      | k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_18298]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_27,negated_conjecture,
% 19.64/3.03      ( ~ r2_hidden(X0,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,sK6(X0)) = X0 ),
% 19.64/3.03      inference(cnf_transformation,[],[f82]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2766,negated_conjecture,
% 19.64/3.03      ( ~ r2_hidden(X0_54,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.03      | k2_yellow_0(sK2,sK6(X0_54)) = X0_54 ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_27]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3493,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,sK6(X0_54)) = X0_54
% 19.64/3.03      | r2_hidden(X0_54,sK4) != iProver_top
% 19.64/3.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(predicate_to_equality,[status(thm)],[c_2766]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4835,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,sK6(sK0(sK2,X0_54,X1_54))) = sK0(sK2,X0_54,X1_54)
% 19.64/3.03      | r1_lattice3(sK2,X0_54,X1_54) = iProver_top
% 19.64/3.03      | r2_hidden(sK0(sK2,X0_54,X1_54),sK4) != iProver_top
% 19.64/3.03      | m1_subset_1(X1_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3516,c_3493]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4957,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_54))) = sK0(sK2,sK4,X0_54)
% 19.64/3.03      | r1_lattice3(sK2,sK4,X0_54) = iProver_top
% 19.64/3.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3517,c_4835]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_5152,plain,
% 19.64/3.03      ( k2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 19.64/3.03      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 19.64/3.03      inference(superposition,[status(thm)],[c_3492,c_4957]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4575,plain,
% 19.64/3.03      ( sK5 = sK5 ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_4176,plain,
% 19.64/3.03      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2775]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_28,negated_conjecture,
% 19.64/3.03      ( r2_yellow_0(sK2,sK6(X0))
% 19.64/3.03      | ~ r2_hidden(X0,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(cnf_transformation,[],[f81]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2765,negated_conjecture,
% 19.64/3.03      ( r2_yellow_0(sK2,sK6(X0_54))
% 19.64/3.03      | ~ r2_hidden(X0_54,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_28]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3998,plain,
% 19.64/3.03      ( r2_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 19.64/3.03      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 19.64/3.03      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2765]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_29,negated_conjecture,
% 19.64/3.03      ( ~ r2_hidden(X0,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 19.64/3.03      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 19.64/3.03      inference(cnf_transformation,[],[f80]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_2764,negated_conjecture,
% 19.64/3.03      ( ~ r2_hidden(X0_54,sK4)
% 19.64/3.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 19.64/3.03      | m1_subset_1(sK6(X0_54),k1_zfmisc_1(sK3)) ),
% 19.64/3.03      inference(subtyping,[status(esa)],[c_29]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3999,plain,
% 19.64/3.03      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 19.64/3.03      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 19.64/3.03      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_2764]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3622,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK4,sK5)
% 19.64/3.03      | r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_3620]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3616,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK4,sK5)
% 19.64/3.03      | ~ r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_3614]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(c_3606,plain,
% 19.64/3.03      ( r1_lattice3(sK2,sK4,sK5)
% 19.64/3.03      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 19.64/3.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 19.64/3.03      inference(instantiation,[status(thm)],[c_3604]) ).
% 19.64/3.03  
% 19.64/3.03  cnf(contradiction,plain,
% 19.64/3.03      ( $false ),
% 19.64/3.03      inference(minisat,
% 19.64/3.03                [status(thm)],
% 19.64/3.03                [c_30304,c_29869,c_28080,c_27769,c_19266,c_19265,c_18536,
% 19.64/3.03                 c_18310,c_5152,c_4575,c_4176,c_3998,c_3999,c_3622,
% 19.64/3.03                 c_3616,c_3606,c_62,c_23,c_60,c_25]) ).
% 19.64/3.03  
% 19.64/3.03  
% 19.64/3.03  % SZS output end CNFRefutation for theBenchmark.p
% 19.64/3.03  
% 19.64/3.03  ------                               Statistics
% 19.64/3.03  
% 19.64/3.03  ------ General
% 19.64/3.03  
% 19.64/3.03  abstr_ref_over_cycles:                  0
% 19.64/3.03  abstr_ref_under_cycles:                 0
% 19.64/3.03  gc_basic_clause_elim:                   0
% 19.64/3.03  forced_gc_time:                         0
% 19.64/3.03  parsing_time:                           0.011
% 19.64/3.03  unif_index_cands_time:                  0.
% 19.64/3.03  unif_index_add_time:                    0.
% 19.64/3.03  orderings_time:                         0.
% 19.64/3.03  out_proof_time:                         0.044
% 19.64/3.03  total_time:                             2.013
% 19.64/3.03  num_of_symbols:                         57
% 19.64/3.03  num_of_terms:                           21269
% 19.64/3.03  
% 19.64/3.03  ------ Preprocessing
% 19.64/3.03  
% 19.64/3.03  num_of_splits:                          2
% 19.64/3.03  num_of_split_atoms:                     2
% 19.64/3.03  num_of_reused_defs:                     0
% 19.64/3.03  num_eq_ax_congr_red:                    38
% 19.64/3.03  num_of_sem_filtered_clauses:            3
% 19.64/3.03  num_of_subtypes:                        2
% 19.64/3.03  monotx_restored_types:                  0
% 19.64/3.03  sat_num_of_epr_types:                   0
% 19.64/3.03  sat_num_of_non_cyclic_types:            0
% 19.64/3.03  sat_guarded_non_collapsed_types:        1
% 19.64/3.03  num_pure_diseq_elim:                    0
% 19.64/3.03  simp_replaced_by:                       0
% 19.64/3.03  res_preprocessed:                       147
% 19.64/3.03  prep_upred:                             0
% 19.64/3.03  prep_unflattend:                        114
% 19.64/3.03  smt_new_axioms:                         0
% 19.64/3.03  pred_elim_cands:                        6
% 19.64/3.03  pred_elim:                              7
% 19.64/3.03  pred_elim_cl:                           8
% 19.64/3.03  pred_elim_cycles:                       11
% 19.64/3.03  merged_defs:                            8
% 19.64/3.03  merged_defs_ncl:                        0
% 19.64/3.03  bin_hyper_res:                          8
% 19.64/3.03  prep_cycles:                            4
% 19.64/3.03  pred_elim_time:                         0.042
% 19.64/3.03  splitting_time:                         0.
% 19.64/3.03  sem_filter_time:                        0.
% 19.64/3.03  monotx_time:                            0.
% 19.64/3.03  subtype_inf_time:                       0.
% 19.64/3.03  
% 19.64/3.03  ------ Problem properties
% 19.64/3.03  
% 19.64/3.03  clauses:                                31
% 19.64/3.03  conjectures:                            8
% 19.64/3.03  epr:                                    3
% 19.64/3.03  horn:                                   22
% 19.64/3.03  ground:                                 6
% 19.64/3.03  unary:                                  4
% 19.64/3.03  binary:                                 5
% 19.64/3.03  lits:                                   97
% 19.64/3.03  lits_eq:                                8
% 19.64/3.03  fd_pure:                                0
% 19.64/3.03  fd_pseudo:                              0
% 19.64/3.03  fd_cond:                                0
% 19.64/3.03  fd_pseudo_cond:                         3
% 19.64/3.03  ac_symbols:                             0
% 19.64/3.03  
% 19.64/3.03  ------ Propositional Solver
% 19.64/3.03  
% 19.64/3.03  prop_solver_calls:                      43
% 19.64/3.03  prop_fast_solver_calls:                 7658
% 19.64/3.03  smt_solver_calls:                       0
% 19.64/3.03  smt_fast_solver_calls:                  0
% 19.64/3.03  prop_num_of_clauses:                    14118
% 19.64/3.03  prop_preprocess_simplified:             21363
% 19.64/3.03  prop_fo_subsumed:                       277
% 19.64/3.03  prop_solver_time:                       0.
% 19.64/3.03  smt_solver_time:                        0.
% 19.64/3.03  smt_fast_solver_time:                   0.
% 19.64/3.03  prop_fast_solver_time:                  0.
% 19.64/3.03  prop_unsat_core_time:                   0.001
% 19.64/3.03  
% 19.64/3.03  ------ QBF
% 19.64/3.03  
% 19.64/3.03  qbf_q_res:                              0
% 19.64/3.03  qbf_num_tautologies:                    0
% 19.64/3.03  qbf_prep_cycles:                        0
% 19.64/3.03  
% 19.64/3.03  ------ BMC1
% 19.64/3.03  
% 19.64/3.03  bmc1_current_bound:                     -1
% 19.64/3.03  bmc1_last_solved_bound:                 -1
% 19.64/3.03  bmc1_unsat_core_size:                   -1
% 19.64/3.03  bmc1_unsat_core_parents_size:           -1
% 19.64/3.03  bmc1_merge_next_fun:                    0
% 19.64/3.03  bmc1_unsat_core_clauses_time:           0.
% 19.64/3.03  
% 19.64/3.03  ------ Instantiation
% 19.64/3.03  
% 19.64/3.03  inst_num_of_clauses:                    199
% 19.64/3.03  inst_num_in_passive:                    80
% 19.64/3.03  inst_num_in_active:                     2290
% 19.64/3.03  inst_num_in_unprocessed:                1
% 19.64/3.03  inst_num_of_loops:                      3121
% 19.64/3.03  inst_num_of_learning_restarts:          1
% 19.64/3.03  inst_num_moves_active_passive:          817
% 19.64/3.03  inst_lit_activity:                      0
% 19.64/3.03  inst_lit_activity_moves:                1
% 19.64/3.03  inst_num_tautologies:                   0
% 19.64/3.03  inst_num_prop_implied:                  0
% 19.64/3.03  inst_num_existing_simplified:           0
% 19.64/3.03  inst_num_eq_res_simplified:             0
% 19.64/3.03  inst_num_child_elim:                    0
% 19.64/3.03  inst_num_of_dismatching_blockings:      1988
% 19.64/3.03  inst_num_of_non_proper_insts:           5371
% 19.64/3.03  inst_num_of_duplicates:                 0
% 19.64/3.03  inst_inst_num_from_inst_to_res:         0
% 19.64/3.03  inst_dismatching_checking_time:         0.
% 19.64/3.03  
% 19.64/3.03  ------ Resolution
% 19.64/3.03  
% 19.64/3.03  res_num_of_clauses:                     39
% 19.64/3.03  res_num_in_passive:                     39
% 19.64/3.03  res_num_in_active:                      0
% 19.64/3.03  res_num_of_loops:                       151
% 19.64/3.03  res_forward_subset_subsumed:            191
% 19.64/3.03  res_backward_subset_subsumed:           0
% 19.64/3.03  res_forward_subsumed:                   0
% 19.64/3.03  res_backward_subsumed:                  0
% 19.64/3.03  res_forward_subsumption_resolution:     3
% 19.64/3.03  res_backward_subsumption_resolution:    0
% 19.64/3.03  res_clause_to_clause_subsumption:       9382
% 19.64/3.03  res_orphan_elimination:                 0
% 19.64/3.03  res_tautology_del:                      494
% 19.64/3.03  res_num_eq_res_simplified:              0
% 19.64/3.03  res_num_sel_changes:                    0
% 19.64/3.03  res_moves_from_active_to_pass:          0
% 19.64/3.03  
% 19.64/3.03  ------ Superposition
% 19.64/3.03  
% 19.64/3.03  sup_time_total:                         0.
% 19.64/3.03  sup_time_generating:                    0.
% 19.64/3.03  sup_time_sim_full:                      0.
% 19.64/3.03  sup_time_sim_immed:                     0.
% 19.64/3.03  
% 19.64/3.03  sup_num_of_clauses:                     915
% 19.64/3.03  sup_num_in_active:                      420
% 19.64/3.03  sup_num_in_passive:                     495
% 19.64/3.03  sup_num_of_loops:                       624
% 19.64/3.03  sup_fw_superposition:                   663
% 19.64/3.03  sup_bw_superposition:                   731
% 19.64/3.03  sup_immediate_simplified:               282
% 19.64/3.03  sup_given_eliminated:                   1
% 19.64/3.03  comparisons_done:                       0
% 19.64/3.03  comparisons_avoided:                    243
% 19.64/3.03  
% 19.64/3.03  ------ Simplifications
% 19.64/3.03  
% 19.64/3.03  
% 19.64/3.03  sim_fw_subset_subsumed:                 156
% 19.64/3.03  sim_bw_subset_subsumed:                 182
% 19.64/3.03  sim_fw_subsumed:                        59
% 19.64/3.03  sim_bw_subsumed:                        123
% 19.64/3.03  sim_fw_subsumption_res:                 0
% 19.64/3.03  sim_bw_subsumption_res:                 0
% 19.64/3.03  sim_tautology_del:                      5
% 19.64/3.03  sim_eq_tautology_del:                   0
% 19.64/3.03  sim_eq_res_simp:                        0
% 19.64/3.03  sim_fw_demodulated:                     2
% 19.64/3.03  sim_bw_demodulated:                     1
% 19.64/3.03  sim_light_normalised:                   2
% 19.64/3.03  sim_joinable_taut:                      0
% 19.64/3.03  sim_joinable_simp:                      0
% 19.64/3.03  sim_ac_normalised:                      0
% 19.64/3.03  sim_smt_subsumption:                    0
% 19.64/3.03  
%------------------------------------------------------------------------------
