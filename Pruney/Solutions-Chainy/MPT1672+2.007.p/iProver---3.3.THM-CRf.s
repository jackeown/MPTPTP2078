%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:09 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  355 (4186 expanded)
%              Number of clauses        :  278 (1091 expanded)
%              Number of leaves         :   23 (1114 expanded)
%              Depth                    :   51
%              Number of atoms          : 1774 (65310 expanded)
%              Number of equality atoms :  668 (9016 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

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
    inference(pure_predicate_removal,[],[f13])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f39,f44,f43,f42,f41,f40])).

fof(f69,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK2,X4),sK4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    ! [X7] :
      ( r1_yellow_0(sK2,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X5] :
      ( k1_yellow_0(sK2,sK6(X5)) = X5
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X5] :
      ( r1_yellow_0(sK2,sK6(X5))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(X5),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2638,plain,
    ( ~ r1_orders_2(X0_52,X0_53,X1_53)
    | r1_orders_2(X0_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_30396,plain,
    ( ~ r1_orders_2(sK2,X0_53,X1_53)
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | sK0(sK2,sK4,sK5) != X0_53
    | sK5 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_30678,plain,
    ( ~ r1_orders_2(sK2,X0_53,sK5)
    | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | sK0(sK2,sK4,sK5) != X0_53
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_30396])).

cnf(c_31294,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_30678])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_715,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_716,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_2610,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_53),X1_53)
    | ~ r1_yellow_0(sK2,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_716])).

cnf(c_18948,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,X0_53,sK5)),X1_53)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),X1_53)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2610])).

cnf(c_29158,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,X0_53,sK5)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_18948])).

cnf(c_29160,plain,
    ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
    | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_29158])).

cnf(c_2633,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_28703,plain,
    ( sK0(sK2,X0_53,sK5) = sK0(sK2,X0_53,sK5) ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_28704,plain,
    ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_28703])).

cnf(c_2636,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_3428,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,u1_struct_0(sK2))
    | X2_53 != X0_53
    | u1_struct_0(sK2) != X1_53 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_3648,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | m1_subset_1(X1_53,u1_struct_0(sK2))
    | X1_53 != X0_53
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_19148,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_53,sK5),u1_struct_0(sK2))
    | X0_53 != sK0(sK2,X1_53,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3648])).

cnf(c_28398,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_19148])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_835,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_836,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_2604,plain,
    ( r2_lattice3(sK2,X0_53,X1_53)
    | r2_hidden(sK0(sK2,X0_53,X1_53),X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_836])).

cnf(c_3344,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r2_hidden(sK0(sK2,X0_53,X1_53),X0_53) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2604])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_820,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_821,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_2605,plain,
    ( r2_lattice3(sK2,X0_53,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_53,X1_53),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_3343,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2605])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2631,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(X1_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3318,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2631])).

cnf(c_22,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2629,negated_conjecture,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3320,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_498,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_499,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_598,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_32])).

cnf(c_599,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_2617,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | r2_lattice3(sK2,X2_53,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_599])).

cnf(c_3331,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r2_lattice3(sK2,X2_53,X1_53) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2617])).

cnf(c_3926,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3320,c_3331])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4041,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3926,c_58])).

cnf(c_4042,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4041])).

cnf(c_4048,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3318,c_4042])).

cnf(c_4056,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_3331])).

cnf(c_4984,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4056,c_58])).

cnf(c_4985,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4984])).

cnf(c_4990,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3318,c_4985])).

cnf(c_4993,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_4990])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_799,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_800,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_2606,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | r1_orders_2(sK2,X2_53,X1_53)
    | ~ r2_hidden(X2_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_800])).

cnf(c_3342,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,X2_53,X1_53) = iProver_top
    | r2_hidden(X2_53,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_6259,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,X2_53,sK5) = iProver_top
    | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_3342])).

cnf(c_11808,plain,
    ( m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
    | r1_orders_2(sK2,X2_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6259,c_58])).

cnf(c_11809,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,X2_53,sK5) = iProver_top
    | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11808])).

cnf(c_11814,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_11809])).

cnf(c_21,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_60,plain,
    ( r2_lattice3(sK2,sK3,sK5) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2652,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_850,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_851,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_2603,plain,
    ( r2_lattice3(sK2,X0_53,X1_53)
    | ~ r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_851])).

cnf(c_3443,plain,
    ( r2_lattice3(sK2,X0_53,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,X0_53,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_3556,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_3557,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3556])).

cnf(c_3449,plain,
    ( r2_lattice3(sK2,X0_53,sK5)
    | r2_hidden(sK0(sK2,X0_53,sK5),X0_53)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_3582,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_3583,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3582])).

cnf(c_3437,plain,
    ( r2_lattice3(sK2,X0_53,sK5)
    | m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_3595,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(c_3596,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3595])).

cnf(c_3411,plain,
    ( ~ r2_hidden(X0_53,sK3)
    | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2631])).

cnf(c_3693,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_3694,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3693])).

cnf(c_3490,plain,
    ( ~ r2_lattice3(sK2,X0_53,sK5)
    | r1_orders_2(sK2,X1_53,sK5)
    | ~ r2_hidden(X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2606])).

cnf(c_3696,plain,
    ( ~ r2_lattice3(sK2,X0_53,sK5)
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
    | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_53)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3490])).

cnf(c_3707,plain,
    ( r2_lattice3(sK2,X0_53,sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),X0_53) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_3709,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3707])).

cnf(c_5,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_458,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_33])).

cnf(c_459,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_463,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_34,c_32])).

cnf(c_2621,plain,
    ( r1_orders_2(sK2,X0_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_3545,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_53,sK5),sK0(sK2,X0_53,sK5))
    | ~ m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_3743,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3545])).

cnf(c_3744,plain,
    ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3743])).

cnf(c_4,plain,
    ( v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_544,plain,
    ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_545,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_2619,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_53)),sK4)
    | ~ m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_53) ),
    inference(subtyping,[status(esa)],[c_545])).

cnf(c_3939,plain,
    ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_3940,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3939])).

cnf(c_29,negated_conjecture,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_529,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | k1_tarski(X1) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_530,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_2620,plain,
    ( r1_yellow_0(sK2,k1_tarski(X0_53))
    | ~ m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(X0_53) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_3938,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
    | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_3942,plain,
    ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3938])).

cnf(c_15,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_682,plain,
    ( r2_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_683,plain,
    ( r2_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_2612,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53)
    | ~ r1_orders_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_683])).

cnf(c_3505,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),sK0(sK2,X1_53,sK5))
    | ~ r1_orders_2(sK2,X0_53,sK0(sK2,X1_53,sK5))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X1_53,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_3716,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_53,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,X0_53,sK5))
    | ~ m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3505])).

cnf(c_3975,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3716])).

cnf(c_3976,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3975])).

cnf(c_6123,plain,
    ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_6567,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_757,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_758,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_2608,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | r2_lattice3(sK2,X0_53,sK1(sK2,X0_53,X1_53))
    | ~ r1_yellow_0(sK2,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_5874,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_6689,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5874])).

cnf(c_6690,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6689])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_736,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_737,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_2609,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | ~ r1_yellow_0(sK2,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_5875,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_6702,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5875])).

cnf(c_6703,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6702])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_778,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_779,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
    | ~ r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_2607,plain,
    ( ~ r2_lattice3(sK2,X0_53,X1_53)
    | ~ r1_orders_2(sK2,X1_53,sK1(sK2,X0_53,X1_53))
    | ~ r1_yellow_0(sK2,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_5873,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
    | ~ r1_orders_2(sK2,X0_53,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_6717,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
    | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5873])).

cnf(c_6718,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6717])).

cnf(c_2634,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4458,plain,
    ( X0_53 != X1_53
    | sK0(sK2,X2_53,sK5) != X1_53
    | sK0(sK2,X2_53,sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_5326,plain,
    ( X0_53 != sK0(sK2,X1_53,sK5)
    | sK0(sK2,X1_53,sK5) = X0_53
    | sK0(sK2,X1_53,sK5) != sK0(sK2,X1_53,sK5) ),
    inference(instantiation,[status(thm)],[c_4458])).

cnf(c_7768,plain,
    ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
    | sK0(sK2,sK3,sK5) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5326])).

cnf(c_4849,plain,
    ( X0_53 != X1_53
    | k1_tarski(sK0(sK2,sK3,sK5)) != X1_53
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_7657,plain,
    ( X0_53 != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = X0_53
    | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_4849])).

cnf(c_8419,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
    | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_7657])).

cnf(c_6260,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_3331])).

cnf(c_8543,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
    | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6260,c_58])).

cnf(c_8544,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8543])).

cnf(c_8549,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X2_53),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3318,c_8544])).

cnf(c_8719,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53)),sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_8549])).

cnf(c_16,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_666,plain,
    ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_667,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_2613,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0_53),X1_53)
    | r1_orders_2(sK2,X0_53,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_3335,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) != iProver_top
    | r1_orders_2(sK2,X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2613])).

cnf(c_11131,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8719,c_3335])).

cnf(c_2637,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_3406,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X2_53,sK4)
    | X2_53 != X0_53
    | sK4 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_5913,plain,
    ( r2_hidden(X0_53,sK4)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | X0_53 != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_11473,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
    | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
    | sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5913])).

cnf(c_11474,plain,
    ( sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
    | sK4 != sK4
    | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
    | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11473])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_452,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_2622,plain,
    ( k1_tarski(X0_53) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_13889,plain,
    ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2622])).

cnf(c_10122,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(X0_53),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,X0_53,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_17752,plain,
    ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
    | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10122])).

cnf(c_17753,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17752])).

cnf(c_24418,plain,
    ( r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11814,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,c_3709,c_3744,c_3940,c_3942,c_3976,c_6123,c_6567,c_6690,c_6703,c_6718,c_7768,c_8419,c_11131,c_11474,c_13889,c_17753])).

cnf(c_24419,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24418])).

cnf(c_24424,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_24419])).

cnf(c_3345,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X1_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2603])).

cnf(c_24476,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24424,c_3345])).

cnf(c_24506,plain,
    ( m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
    | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24476,c_58])).

cnf(c_24507,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24506])).

cnf(c_24517,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(X0_53),X1_53),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24507,c_3335])).

cnf(c_4261,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_3342])).

cnf(c_6640,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
    | r1_orders_2(sK2,X0_53,sK5) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4261,c_58])).

cnf(c_6641,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
    | r2_hidden(X1_53,sK3) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6640])).

cnf(c_6645,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),sK5) = iProver_top
    | r2_hidden(X2_53,sK3) != iProver_top
    | r2_hidden(sK0(sK2,X0_53,X1_53),k1_tarski(X2_53)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_6641])).

cnf(c_7130,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_6645])).

cnf(c_24656,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24517,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,c_3709,c_3744,c_3940,c_3942,c_3976,c_6123,c_6567,c_6690,c_6703,c_6718,c_7130,c_7768,c_8419,c_11474,c_13889,c_17753])).

cnf(c_24662,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24656,c_3345])).

cnf(c_24780,plain,
    ( r2_hidden(X0_53,sK3) != iProver_top
    | r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24662,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,c_3709,c_3744,c_3940,c_3942,c_3976,c_4048,c_6123,c_6567,c_6690,c_6703,c_6718,c_7768,c_8419,c_11474,c_13889,c_17753])).

cnf(c_24781,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_24780])).

cnf(c_24791,plain,
    ( r1_orders_2(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24781,c_3335])).

cnf(c_24807,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | r1_orders_2(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24791,c_58])).

cnf(c_24808,plain,
    ( r1_orders_2(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(X0_53,sK3) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24807])).

cnf(c_24814,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_53,X1_53),sK3) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_24808])).

cnf(c_25403,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24814,c_3345])).

cnf(c_25422,plain,
    ( r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top
    | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25403,c_58])).

cnf(c_25423,plain,
    ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_25422])).

cnf(c_25426,plain,
    ( r2_lattice3(sK2,sK3,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_25423])).

cnf(c_25427,plain,
    ( r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25426])).

cnf(c_2628,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3321,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2627,negated_conjecture,
    ( ~ r2_hidden(X0_53,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK6(X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3322,plain,
    ( k1_yellow_0(sK2,sK6(X0_53)) = X0_53
    | r2_hidden(X0_53,sK4) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_4506,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,X1_53))) = sK0(sK2,X0_53,X1_53)
    | r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r2_hidden(sK0(sK2,X0_53,X1_53),sK4) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_3322])).

cnf(c_4658,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_53))) = sK0(sK2,sK4,X0_53)
    | r2_lattice3(sK2,sK4,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_4506])).

cnf(c_4663,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_4658])).

cnf(c_3339,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_3336,plain,
    ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2612])).

cnf(c_4260,plain,
    ( r1_orders_2(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,X2_53,X1_53) = iProver_top
    | r2_hidden(X2_53,k1_tarski(X0_53)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3336,c_3342])).

cnf(c_4880,plain,
    ( r1_orders_2(sK2,X0_53,X1_53) = iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_4260])).

cnf(c_5062,plain,
    ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X2_53) = iProver_top
    | r1_orders_2(sK2,sK5,X2_53) != iProver_top
    | r2_hidden(sK0(sK2,X0_53,X1_53),k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_4880])).

cnf(c_7185,plain,
    ( r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK5),X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_5062])).

cnf(c_7287,plain,
    ( r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
    | r1_orders_2(sK2,sK5,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7185,c_3345])).

cnf(c_3340,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r2_lattice3(sK2,X0_53,sK1(sK2,X0_53,X1_53)) = iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2608])).

cnf(c_4784,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r2_hidden(X2_53,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_3342])).

cnf(c_2699,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_8626,plain,
    ( m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2_53,X0_53) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | k1_yellow_0(sK2,X0_53) = X1_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4784,c_2699])).

cnf(c_8627,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r2_hidden(X2_53,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8626])).

cnf(c_3341,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,X1_53,sK1(sK2,X0_53,X1_53)) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2607])).

cnf(c_8634,plain,
    ( k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r2_hidden(X1_53,X0_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8627,c_3341])).

cnf(c_8827,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK5)) = X0_53
    | r1_orders_2(sK2,sK5,X0_53) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7287,c_8634])).

cnf(c_3327,plain,
    ( r1_orders_2(sK2,X0_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_3819,plain,
    ( r1_orders_2(sK2,sK5,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3327])).

cnf(c_17,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_648,plain,
    ( r1_lattice3(X0,k1_tarski(X1),X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_649,plain,
    ( r1_lattice3(sK2,k1_tarski(X0),X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_2614,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53)
    | ~ r1_orders_2(sK2,X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_649])).

cnf(c_3334,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
    | r1_orders_2(sK2,X1_53,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2614])).

cnf(c_20,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_479,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ l1_orders_2(X0)
    | X3 != X4
    | X1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_480,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_614,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_480,c_32])).

cnf(c_615,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_2616,plain,
    ( ~ r1_lattice3(sK2,X0_53,X1_53)
    | r1_lattice3(sK2,X2_53,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_615])).

cnf(c_3332,plain,
    ( r1_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_lattice3(sK2,X2_53,X1_53) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2616])).

cnf(c_3931,plain,
    ( r1_lattice3(sK2,X0_53,sK5) != iProver_top
    | r1_lattice3(sK2,X1_53,sK5) = iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3332])).

cnf(c_4098,plain,
    ( r1_lattice3(sK2,X0_53,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3334,c_3931])).

cnf(c_4852,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | r1_lattice3(sK2,X0_53,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4098,c_58])).

cnf(c_4853,plain,
    ( r1_lattice3(sK2,X0_53,sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4852])).

cnf(c_4858,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r1_orders_2(sK2,sK5,X1_53) != iProver_top
    | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3318,c_4853])).

cnf(c_5056,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3819,c_4858])).

cnf(c_5153,plain,
    ( r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5056,c_58])).

cnf(c_5154,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5153])).

cnf(c_18,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_630,plain,
    ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_631,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
    | r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_2615,plain,
    ( ~ r1_lattice3(sK2,k1_tarski(X0_53),X1_53)
    | r1_orders_2(sK2,X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_3333,plain,
    ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53) != iProver_top
    | r1_orders_2(sK2,X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2615])).

cnf(c_5159,plain,
    ( r1_orders_2(sK2,sK5,X0_53) = iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5154,c_3333])).

cnf(c_21983,plain,
    ( k1_yellow_0(sK2,k1_tarski(sK5)) = X0_53
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8827,c_58,c_5159])).

cnf(c_21989,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_53),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3344,c_21983])).

cnf(c_22193,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_21989])).

cnf(c_22202,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r1_orders_2(sK2,sK5,X0_53) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22193,c_3335])).

cnf(c_22256,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_orders_2(sK2,sK5,X0_53) = iProver_top
    | sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22202,c_58])).

cnf(c_22257,plain,
    ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
    | r1_orders_2(sK2,sK5,X0_53) = iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22256])).

cnf(c_22264,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,X1_53)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_53) = X1_53
    | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
    | r1_orders_2(sK2,sK5,sK1(sK2,X0_53,X1_53)) = iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3339,c_22257])).

cnf(c_22417,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_53) = sK5
    | r2_lattice3(sK2,X0_53,sK5) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22264,c_3341])).

cnf(c_22441,plain,
    ( r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r2_lattice3(sK2,X0_53,sK5) != iProver_top
    | k1_yellow_0(sK2,X0_53) = sK5
    | sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22417,c_58])).

cnf(c_22442,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,X0_53) = sK5
    | r2_lattice3(sK2,X0_53,sK5) != iProver_top
    | r1_yellow_0(sK2,X0_53) != iProver_top
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22441])).

cnf(c_22447,plain,
    ( sK0(sK2,k1_tarski(sK5),sK1(sK2,sK4,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
    | k1_yellow_0(sK2,sK4) = sK5
    | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
    | r1_yellow_0(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4663,c_22442])).

cnf(c_22702,plain,
    ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22447,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,c_3709,c_3744,c_3940,c_3942,c_3976,c_4663,c_6123,c_6567,c_6690,c_6703,c_6718,c_7768,c_8419,c_11474,c_13889,c_17753])).

cnf(c_3486,plain,
    ( ~ r2_lattice3(sK2,X0_53,sK5)
    | r2_lattice3(sK2,X1_53,sK5)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X0_53))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2617])).

cnf(c_3859,plain,
    ( r2_lattice3(sK2,X0_53,sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3486])).

cnf(c_19220,plain,
    ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
    | ~ r2_lattice3(sK2,sK3,sK5)
    | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_19016,plain,
    ( sK0(sK2,X0_53,sK5) != sK0(sK2,X0_53,sK5)
    | sK0(sK2,X0_53,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))) != sK0(sK2,X0_53,sK5) ),
    inference(instantiation,[status(thm)],[c_5326])).

cnf(c_19028,plain,
    ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
    | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_19016])).

cnf(c_4397,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_3989,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_26,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2626,negated_conjecture,
    ( r1_yellow_0(sK2,sK6(X0_53))
    | ~ r2_hidden(X0_53,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3825,plain,
    ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
    | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2625,negated_conjecture,
    ( ~ r2_hidden(X0_53,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | m1_subset_1(sK6(X0_53),k1_zfmisc_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3826,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2625])).

cnf(c_3451,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_3445,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_3439,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31294,c_29160,c_28704,c_28398,c_25427,c_22702,c_19220,c_19028,c_4397,c_3989,c_3825,c_3826,c_3451,c_3445,c_3439,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:59:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.99/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.99/1.98  
% 11.99/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.99/1.98  
% 11.99/1.98  ------  iProver source info
% 11.99/1.98  
% 11.99/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.99/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.99/1.98  git: non_committed_changes: false
% 11.99/1.98  git: last_make_outside_of_git: false
% 11.99/1.98  
% 11.99/1.98  ------ 
% 11.99/1.98  
% 11.99/1.98  ------ Input Options
% 11.99/1.98  
% 11.99/1.98  --out_options                           all
% 11.99/1.98  --tptp_safe_out                         true
% 11.99/1.98  --problem_path                          ""
% 11.99/1.98  --include_path                          ""
% 11.99/1.98  --clausifier                            res/vclausify_rel
% 11.99/1.98  --clausifier_options                    ""
% 11.99/1.98  --stdin                                 false
% 11.99/1.98  --stats_out                             all
% 11.99/1.98  
% 11.99/1.98  ------ General Options
% 11.99/1.98  
% 11.99/1.98  --fof                                   false
% 11.99/1.98  --time_out_real                         305.
% 11.99/1.98  --time_out_virtual                      -1.
% 11.99/1.98  --symbol_type_check                     false
% 11.99/1.98  --clausify_out                          false
% 11.99/1.98  --sig_cnt_out                           false
% 11.99/1.98  --trig_cnt_out                          false
% 11.99/1.98  --trig_cnt_out_tolerance                1.
% 11.99/1.98  --trig_cnt_out_sk_spl                   false
% 11.99/1.98  --abstr_cl_out                          false
% 11.99/1.98  
% 11.99/1.98  ------ Global Options
% 11.99/1.98  
% 11.99/1.98  --schedule                              default
% 11.99/1.98  --add_important_lit                     false
% 11.99/1.98  --prop_solver_per_cl                    1000
% 11.99/1.98  --min_unsat_core                        false
% 11.99/1.98  --soft_assumptions                      false
% 11.99/1.98  --soft_lemma_size                       3
% 11.99/1.98  --prop_impl_unit_size                   0
% 11.99/1.98  --prop_impl_unit                        []
% 11.99/1.98  --share_sel_clauses                     true
% 11.99/1.98  --reset_solvers                         false
% 11.99/1.98  --bc_imp_inh                            [conj_cone]
% 11.99/1.98  --conj_cone_tolerance                   3.
% 11.99/1.98  --extra_neg_conj                        none
% 11.99/1.98  --large_theory_mode                     true
% 11.99/1.98  --prolific_symb_bound                   200
% 11.99/1.98  --lt_threshold                          2000
% 11.99/1.98  --clause_weak_htbl                      true
% 11.99/1.98  --gc_record_bc_elim                     false
% 11.99/1.98  
% 11.99/1.98  ------ Preprocessing Options
% 11.99/1.98  
% 11.99/1.98  --preprocessing_flag                    true
% 11.99/1.98  --time_out_prep_mult                    0.1
% 11.99/1.98  --splitting_mode                        input
% 11.99/1.98  --splitting_grd                         true
% 11.99/1.98  --splitting_cvd                         false
% 11.99/1.98  --splitting_cvd_svl                     false
% 11.99/1.98  --splitting_nvd                         32
% 11.99/1.98  --sub_typing                            true
% 11.99/1.98  --prep_gs_sim                           true
% 11.99/1.98  --prep_unflatten                        true
% 11.99/1.98  --prep_res_sim                          true
% 11.99/1.98  --prep_upred                            true
% 11.99/1.98  --prep_sem_filter                       exhaustive
% 11.99/1.98  --prep_sem_filter_out                   false
% 11.99/1.98  --pred_elim                             true
% 11.99/1.98  --res_sim_input                         true
% 11.99/1.98  --eq_ax_congr_red                       true
% 11.99/1.98  --pure_diseq_elim                       true
% 11.99/1.98  --brand_transform                       false
% 11.99/1.98  --non_eq_to_eq                          false
% 11.99/1.98  --prep_def_merge                        true
% 11.99/1.98  --prep_def_merge_prop_impl              false
% 11.99/1.98  --prep_def_merge_mbd                    true
% 11.99/1.98  --prep_def_merge_tr_red                 false
% 11.99/1.98  --prep_def_merge_tr_cl                  false
% 11.99/1.98  --smt_preprocessing                     true
% 11.99/1.98  --smt_ac_axioms                         fast
% 11.99/1.98  --preprocessed_out                      false
% 11.99/1.98  --preprocessed_stats                    false
% 11.99/1.98  
% 11.99/1.98  ------ Abstraction refinement Options
% 11.99/1.98  
% 11.99/1.98  --abstr_ref                             []
% 11.99/1.98  --abstr_ref_prep                        false
% 11.99/1.98  --abstr_ref_until_sat                   false
% 11.99/1.98  --abstr_ref_sig_restrict                funpre
% 11.99/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/1.98  --abstr_ref_under                       []
% 11.99/1.98  
% 11.99/1.98  ------ SAT Options
% 11.99/1.98  
% 11.99/1.98  --sat_mode                              false
% 11.99/1.98  --sat_fm_restart_options                ""
% 11.99/1.98  --sat_gr_def                            false
% 11.99/1.98  --sat_epr_types                         true
% 11.99/1.98  --sat_non_cyclic_types                  false
% 11.99/1.98  --sat_finite_models                     false
% 11.99/1.98  --sat_fm_lemmas                         false
% 11.99/1.98  --sat_fm_prep                           false
% 11.99/1.98  --sat_fm_uc_incr                        true
% 11.99/1.98  --sat_out_model                         small
% 11.99/1.98  --sat_out_clauses                       false
% 11.99/1.98  
% 11.99/1.98  ------ QBF Options
% 11.99/1.98  
% 11.99/1.98  --qbf_mode                              false
% 11.99/1.98  --qbf_elim_univ                         false
% 11.99/1.98  --qbf_dom_inst                          none
% 11.99/1.98  --qbf_dom_pre_inst                      false
% 11.99/1.98  --qbf_sk_in                             false
% 11.99/1.98  --qbf_pred_elim                         true
% 11.99/1.98  --qbf_split                             512
% 11.99/1.98  
% 11.99/1.98  ------ BMC1 Options
% 11.99/1.98  
% 11.99/1.98  --bmc1_incremental                      false
% 11.99/1.98  --bmc1_axioms                           reachable_all
% 11.99/1.98  --bmc1_min_bound                        0
% 11.99/1.98  --bmc1_max_bound                        -1
% 11.99/1.98  --bmc1_max_bound_default                -1
% 11.99/1.98  --bmc1_symbol_reachability              true
% 11.99/1.98  --bmc1_property_lemmas                  false
% 11.99/1.98  --bmc1_k_induction                      false
% 11.99/1.98  --bmc1_non_equiv_states                 false
% 11.99/1.98  --bmc1_deadlock                         false
% 11.99/1.98  --bmc1_ucm                              false
% 11.99/1.98  --bmc1_add_unsat_core                   none
% 11.99/1.98  --bmc1_unsat_core_children              false
% 11.99/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/1.98  --bmc1_out_stat                         full
% 11.99/1.98  --bmc1_ground_init                      false
% 11.99/1.98  --bmc1_pre_inst_next_state              false
% 11.99/1.98  --bmc1_pre_inst_state                   false
% 11.99/1.98  --bmc1_pre_inst_reach_state             false
% 11.99/1.98  --bmc1_out_unsat_core                   false
% 11.99/1.98  --bmc1_aig_witness_out                  false
% 11.99/1.98  --bmc1_verbose                          false
% 11.99/1.98  --bmc1_dump_clauses_tptp                false
% 11.99/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.99/1.98  --bmc1_dump_file                        -
% 11.99/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.99/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.99/1.98  --bmc1_ucm_extend_mode                  1
% 11.99/1.98  --bmc1_ucm_init_mode                    2
% 11.99/1.98  --bmc1_ucm_cone_mode                    none
% 11.99/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.99/1.98  --bmc1_ucm_relax_model                  4
% 11.99/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.99/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/1.98  --bmc1_ucm_layered_model                none
% 11.99/1.98  --bmc1_ucm_max_lemma_size               10
% 11.99/1.98  
% 11.99/1.98  ------ AIG Options
% 11.99/1.98  
% 11.99/1.98  --aig_mode                              false
% 11.99/1.98  
% 11.99/1.98  ------ Instantiation Options
% 11.99/1.98  
% 11.99/1.98  --instantiation_flag                    true
% 11.99/1.98  --inst_sos_flag                         true
% 11.99/1.98  --inst_sos_phase                        true
% 11.99/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/1.98  --inst_lit_sel_side                     num_symb
% 11.99/1.98  --inst_solver_per_active                1400
% 11.99/1.98  --inst_solver_calls_frac                1.
% 11.99/1.98  --inst_passive_queue_type               priority_queues
% 11.99/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/1.98  --inst_passive_queues_freq              [25;2]
% 11.99/1.98  --inst_dismatching                      true
% 11.99/1.98  --inst_eager_unprocessed_to_passive     true
% 11.99/1.98  --inst_prop_sim_given                   true
% 11.99/1.98  --inst_prop_sim_new                     false
% 11.99/1.98  --inst_subs_new                         false
% 11.99/1.98  --inst_eq_res_simp                      false
% 11.99/1.98  --inst_subs_given                       false
% 11.99/1.98  --inst_orphan_elimination               true
% 11.99/1.98  --inst_learning_loop_flag               true
% 11.99/1.98  --inst_learning_start                   3000
% 11.99/1.98  --inst_learning_factor                  2
% 11.99/1.98  --inst_start_prop_sim_after_learn       3
% 11.99/1.98  --inst_sel_renew                        solver
% 11.99/1.98  --inst_lit_activity_flag                true
% 11.99/1.98  --inst_restr_to_given                   false
% 11.99/1.98  --inst_activity_threshold               500
% 11.99/1.98  --inst_out_proof                        true
% 11.99/1.98  
% 11.99/1.98  ------ Resolution Options
% 11.99/1.98  
% 11.99/1.98  --resolution_flag                       true
% 11.99/1.98  --res_lit_sel                           adaptive
% 11.99/1.98  --res_lit_sel_side                      none
% 11.99/1.98  --res_ordering                          kbo
% 11.99/1.98  --res_to_prop_solver                    active
% 11.99/1.98  --res_prop_simpl_new                    false
% 11.99/1.98  --res_prop_simpl_given                  true
% 11.99/1.98  --res_passive_queue_type                priority_queues
% 11.99/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/1.98  --res_passive_queues_freq               [15;5]
% 11.99/1.98  --res_forward_subs                      full
% 11.99/1.98  --res_backward_subs                     full
% 11.99/1.98  --res_forward_subs_resolution           true
% 11.99/1.98  --res_backward_subs_resolution          true
% 11.99/1.98  --res_orphan_elimination                true
% 11.99/1.98  --res_time_limit                        2.
% 11.99/1.98  --res_out_proof                         true
% 11.99/1.98  
% 11.99/1.98  ------ Superposition Options
% 11.99/1.98  
% 11.99/1.98  --superposition_flag                    true
% 11.99/1.98  --sup_passive_queue_type                priority_queues
% 11.99/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.99/1.98  --demod_completeness_check              fast
% 11.99/1.98  --demod_use_ground                      true
% 11.99/1.98  --sup_to_prop_solver                    passive
% 11.99/1.98  --sup_prop_simpl_new                    true
% 11.99/1.98  --sup_prop_simpl_given                  true
% 11.99/1.98  --sup_fun_splitting                     true
% 11.99/1.98  --sup_smt_interval                      50000
% 11.99/1.98  
% 11.99/1.98  ------ Superposition Simplification Setup
% 11.99/1.98  
% 11.99/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/1.98  --sup_immed_triv                        [TrivRules]
% 11.99/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_immed_bw_main                     []
% 11.99/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_input_bw                          []
% 11.99/1.98  
% 11.99/1.98  ------ Combination Options
% 11.99/1.98  
% 11.99/1.98  --comb_res_mult                         3
% 11.99/1.98  --comb_sup_mult                         2
% 11.99/1.98  --comb_inst_mult                        10
% 11.99/1.98  
% 11.99/1.98  ------ Debug Options
% 11.99/1.98  
% 11.99/1.98  --dbg_backtrace                         false
% 11.99/1.98  --dbg_dump_prop_clauses                 false
% 11.99/1.98  --dbg_dump_prop_clauses_file            -
% 11.99/1.98  --dbg_out_stat                          false
% 11.99/1.98  ------ Parsing...
% 11.99/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.99/1.98  
% 11.99/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.99/1.98  
% 11.99/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.99/1.98  
% 11.99/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.99/1.98  ------ Proving...
% 11.99/1.98  ------ Problem Properties 
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  clauses                                 29
% 11.99/1.98  conjectures                             8
% 11.99/1.98  EPR                                     2
% 11.99/1.98  Horn                                    21
% 11.99/1.98  unary                                   4
% 11.99/1.98  binary                                  4
% 11.99/1.98  lits                                    92
% 11.99/1.98  lits eq                                 8
% 11.99/1.98  fd_pure                                 0
% 11.99/1.98  fd_pseudo                               0
% 11.99/1.98  fd_cond                                 0
% 11.99/1.98  fd_pseudo_cond                          3
% 11.99/1.98  AC symbols                              0
% 11.99/1.98  
% 11.99/1.98  ------ Schedule dynamic 5 is on 
% 11.99/1.98  
% 11.99/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  ------ 
% 11.99/1.98  Current options:
% 11.99/1.98  ------ 
% 11.99/1.98  
% 11.99/1.98  ------ Input Options
% 11.99/1.98  
% 11.99/1.98  --out_options                           all
% 11.99/1.98  --tptp_safe_out                         true
% 11.99/1.98  --problem_path                          ""
% 11.99/1.98  --include_path                          ""
% 11.99/1.98  --clausifier                            res/vclausify_rel
% 11.99/1.98  --clausifier_options                    ""
% 11.99/1.98  --stdin                                 false
% 11.99/1.98  --stats_out                             all
% 11.99/1.98  
% 11.99/1.98  ------ General Options
% 11.99/1.98  
% 11.99/1.98  --fof                                   false
% 11.99/1.98  --time_out_real                         305.
% 11.99/1.98  --time_out_virtual                      -1.
% 11.99/1.98  --symbol_type_check                     false
% 11.99/1.98  --clausify_out                          false
% 11.99/1.98  --sig_cnt_out                           false
% 11.99/1.98  --trig_cnt_out                          false
% 11.99/1.98  --trig_cnt_out_tolerance                1.
% 11.99/1.98  --trig_cnt_out_sk_spl                   false
% 11.99/1.98  --abstr_cl_out                          false
% 11.99/1.98  
% 11.99/1.98  ------ Global Options
% 11.99/1.98  
% 11.99/1.98  --schedule                              default
% 11.99/1.98  --add_important_lit                     false
% 11.99/1.98  --prop_solver_per_cl                    1000
% 11.99/1.98  --min_unsat_core                        false
% 11.99/1.98  --soft_assumptions                      false
% 11.99/1.98  --soft_lemma_size                       3
% 11.99/1.98  --prop_impl_unit_size                   0
% 11.99/1.98  --prop_impl_unit                        []
% 11.99/1.98  --share_sel_clauses                     true
% 11.99/1.98  --reset_solvers                         false
% 11.99/1.98  --bc_imp_inh                            [conj_cone]
% 11.99/1.98  --conj_cone_tolerance                   3.
% 11.99/1.98  --extra_neg_conj                        none
% 11.99/1.98  --large_theory_mode                     true
% 11.99/1.98  --prolific_symb_bound                   200
% 11.99/1.98  --lt_threshold                          2000
% 11.99/1.98  --clause_weak_htbl                      true
% 11.99/1.98  --gc_record_bc_elim                     false
% 11.99/1.98  
% 11.99/1.98  ------ Preprocessing Options
% 11.99/1.98  
% 11.99/1.98  --preprocessing_flag                    true
% 11.99/1.98  --time_out_prep_mult                    0.1
% 11.99/1.98  --splitting_mode                        input
% 11.99/1.98  --splitting_grd                         true
% 11.99/1.98  --splitting_cvd                         false
% 11.99/1.98  --splitting_cvd_svl                     false
% 11.99/1.98  --splitting_nvd                         32
% 11.99/1.98  --sub_typing                            true
% 11.99/1.98  --prep_gs_sim                           true
% 11.99/1.98  --prep_unflatten                        true
% 11.99/1.98  --prep_res_sim                          true
% 11.99/1.98  --prep_upred                            true
% 11.99/1.98  --prep_sem_filter                       exhaustive
% 11.99/1.98  --prep_sem_filter_out                   false
% 11.99/1.98  --pred_elim                             true
% 11.99/1.98  --res_sim_input                         true
% 11.99/1.98  --eq_ax_congr_red                       true
% 11.99/1.98  --pure_diseq_elim                       true
% 11.99/1.98  --brand_transform                       false
% 11.99/1.98  --non_eq_to_eq                          false
% 11.99/1.98  --prep_def_merge                        true
% 11.99/1.98  --prep_def_merge_prop_impl              false
% 11.99/1.98  --prep_def_merge_mbd                    true
% 11.99/1.98  --prep_def_merge_tr_red                 false
% 11.99/1.98  --prep_def_merge_tr_cl                  false
% 11.99/1.98  --smt_preprocessing                     true
% 11.99/1.98  --smt_ac_axioms                         fast
% 11.99/1.98  --preprocessed_out                      false
% 11.99/1.98  --preprocessed_stats                    false
% 11.99/1.98  
% 11.99/1.98  ------ Abstraction refinement Options
% 11.99/1.98  
% 11.99/1.98  --abstr_ref                             []
% 11.99/1.98  --abstr_ref_prep                        false
% 11.99/1.98  --abstr_ref_until_sat                   false
% 11.99/1.98  --abstr_ref_sig_restrict                funpre
% 11.99/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/1.98  --abstr_ref_under                       []
% 11.99/1.98  
% 11.99/1.98  ------ SAT Options
% 11.99/1.98  
% 11.99/1.98  --sat_mode                              false
% 11.99/1.98  --sat_fm_restart_options                ""
% 11.99/1.98  --sat_gr_def                            false
% 11.99/1.98  --sat_epr_types                         true
% 11.99/1.98  --sat_non_cyclic_types                  false
% 11.99/1.98  --sat_finite_models                     false
% 11.99/1.98  --sat_fm_lemmas                         false
% 11.99/1.98  --sat_fm_prep                           false
% 11.99/1.98  --sat_fm_uc_incr                        true
% 11.99/1.98  --sat_out_model                         small
% 11.99/1.98  --sat_out_clauses                       false
% 11.99/1.98  
% 11.99/1.98  ------ QBF Options
% 11.99/1.98  
% 11.99/1.98  --qbf_mode                              false
% 11.99/1.98  --qbf_elim_univ                         false
% 11.99/1.98  --qbf_dom_inst                          none
% 11.99/1.98  --qbf_dom_pre_inst                      false
% 11.99/1.98  --qbf_sk_in                             false
% 11.99/1.98  --qbf_pred_elim                         true
% 11.99/1.98  --qbf_split                             512
% 11.99/1.98  
% 11.99/1.98  ------ BMC1 Options
% 11.99/1.98  
% 11.99/1.98  --bmc1_incremental                      false
% 11.99/1.98  --bmc1_axioms                           reachable_all
% 11.99/1.98  --bmc1_min_bound                        0
% 11.99/1.98  --bmc1_max_bound                        -1
% 11.99/1.98  --bmc1_max_bound_default                -1
% 11.99/1.98  --bmc1_symbol_reachability              true
% 11.99/1.98  --bmc1_property_lemmas                  false
% 11.99/1.98  --bmc1_k_induction                      false
% 11.99/1.98  --bmc1_non_equiv_states                 false
% 11.99/1.98  --bmc1_deadlock                         false
% 11.99/1.98  --bmc1_ucm                              false
% 11.99/1.98  --bmc1_add_unsat_core                   none
% 11.99/1.98  --bmc1_unsat_core_children              false
% 11.99/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/1.98  --bmc1_out_stat                         full
% 11.99/1.98  --bmc1_ground_init                      false
% 11.99/1.98  --bmc1_pre_inst_next_state              false
% 11.99/1.98  --bmc1_pre_inst_state                   false
% 11.99/1.98  --bmc1_pre_inst_reach_state             false
% 11.99/1.98  --bmc1_out_unsat_core                   false
% 11.99/1.98  --bmc1_aig_witness_out                  false
% 11.99/1.98  --bmc1_verbose                          false
% 11.99/1.98  --bmc1_dump_clauses_tptp                false
% 11.99/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.99/1.98  --bmc1_dump_file                        -
% 11.99/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.99/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.99/1.98  --bmc1_ucm_extend_mode                  1
% 11.99/1.98  --bmc1_ucm_init_mode                    2
% 11.99/1.98  --bmc1_ucm_cone_mode                    none
% 11.99/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.99/1.98  --bmc1_ucm_relax_model                  4
% 11.99/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.99/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/1.98  --bmc1_ucm_layered_model                none
% 11.99/1.98  --bmc1_ucm_max_lemma_size               10
% 11.99/1.98  
% 11.99/1.98  ------ AIG Options
% 11.99/1.98  
% 11.99/1.98  --aig_mode                              false
% 11.99/1.98  
% 11.99/1.98  ------ Instantiation Options
% 11.99/1.98  
% 11.99/1.98  --instantiation_flag                    true
% 11.99/1.98  --inst_sos_flag                         true
% 11.99/1.98  --inst_sos_phase                        true
% 11.99/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/1.98  --inst_lit_sel_side                     none
% 11.99/1.98  --inst_solver_per_active                1400
% 11.99/1.98  --inst_solver_calls_frac                1.
% 11.99/1.98  --inst_passive_queue_type               priority_queues
% 11.99/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/1.98  --inst_passive_queues_freq              [25;2]
% 11.99/1.98  --inst_dismatching                      true
% 11.99/1.98  --inst_eager_unprocessed_to_passive     true
% 11.99/1.98  --inst_prop_sim_given                   true
% 11.99/1.98  --inst_prop_sim_new                     false
% 11.99/1.98  --inst_subs_new                         false
% 11.99/1.98  --inst_eq_res_simp                      false
% 11.99/1.98  --inst_subs_given                       false
% 11.99/1.98  --inst_orphan_elimination               true
% 11.99/1.98  --inst_learning_loop_flag               true
% 11.99/1.98  --inst_learning_start                   3000
% 11.99/1.98  --inst_learning_factor                  2
% 11.99/1.98  --inst_start_prop_sim_after_learn       3
% 11.99/1.98  --inst_sel_renew                        solver
% 11.99/1.98  --inst_lit_activity_flag                true
% 11.99/1.98  --inst_restr_to_given                   false
% 11.99/1.98  --inst_activity_threshold               500
% 11.99/1.98  --inst_out_proof                        true
% 11.99/1.98  
% 11.99/1.98  ------ Resolution Options
% 11.99/1.98  
% 11.99/1.98  --resolution_flag                       false
% 11.99/1.98  --res_lit_sel                           adaptive
% 11.99/1.98  --res_lit_sel_side                      none
% 11.99/1.98  --res_ordering                          kbo
% 11.99/1.98  --res_to_prop_solver                    active
% 11.99/1.98  --res_prop_simpl_new                    false
% 11.99/1.98  --res_prop_simpl_given                  true
% 11.99/1.98  --res_passive_queue_type                priority_queues
% 11.99/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/1.98  --res_passive_queues_freq               [15;5]
% 11.99/1.98  --res_forward_subs                      full
% 11.99/1.98  --res_backward_subs                     full
% 11.99/1.98  --res_forward_subs_resolution           true
% 11.99/1.98  --res_backward_subs_resolution          true
% 11.99/1.98  --res_orphan_elimination                true
% 11.99/1.98  --res_time_limit                        2.
% 11.99/1.98  --res_out_proof                         true
% 11.99/1.98  
% 11.99/1.98  ------ Superposition Options
% 11.99/1.98  
% 11.99/1.98  --superposition_flag                    true
% 11.99/1.98  --sup_passive_queue_type                priority_queues
% 11.99/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.99/1.98  --demod_completeness_check              fast
% 11.99/1.98  --demod_use_ground                      true
% 11.99/1.98  --sup_to_prop_solver                    passive
% 11.99/1.98  --sup_prop_simpl_new                    true
% 11.99/1.98  --sup_prop_simpl_given                  true
% 11.99/1.98  --sup_fun_splitting                     true
% 11.99/1.98  --sup_smt_interval                      50000
% 11.99/1.98  
% 11.99/1.98  ------ Superposition Simplification Setup
% 11.99/1.98  
% 11.99/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/1.98  --sup_immed_triv                        [TrivRules]
% 11.99/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_immed_bw_main                     []
% 11.99/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/1.98  --sup_input_bw                          []
% 11.99/1.98  
% 11.99/1.98  ------ Combination Options
% 11.99/1.98  
% 11.99/1.98  --comb_res_mult                         3
% 11.99/1.98  --comb_sup_mult                         2
% 11.99/1.98  --comb_inst_mult                        10
% 11.99/1.98  
% 11.99/1.98  ------ Debug Options
% 11.99/1.98  
% 11.99/1.98  --dbg_backtrace                         false
% 11.99/1.98  --dbg_dump_prop_clauses                 false
% 11.99/1.98  --dbg_dump_prop_clauses_file            -
% 11.99/1.98  --dbg_out_stat                          false
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  ------ Proving...
% 11.99/1.98  
% 11.99/1.98  
% 11.99/1.98  % SZS status Theorem for theBenchmark.p
% 11.99/1.98  
% 11.99/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.99/1.98  
% 11.99/1.98  fof(f8,axiom,(
% 11.99/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f22,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(ennf_transformation,[],[f8])).
% 11.99/1.98  
% 11.99/1.98  fof(f23,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(flattening,[],[f22])).
% 11.99/1.98  
% 11.99/1.98  fof(f32,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(nnf_transformation,[],[f23])).
% 11.99/1.98  
% 11.99/1.98  fof(f33,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(flattening,[],[f32])).
% 11.99/1.98  
% 11.99/1.98  fof(f34,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(rectify,[],[f33])).
% 11.99/1.98  
% 11.99/1.98  fof(f35,plain,(
% 11.99/1.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f36,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 11.99/1.98  
% 11.99/1.98  fof(f57,plain,(
% 11.99/1.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f36])).
% 11.99/1.98  
% 11.99/1.98  fof(f81,plain,(
% 11.99/1.98    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(equality_resolution,[],[f57])).
% 11.99/1.98  
% 11.99/1.98  fof(f11,conjecture,(
% 11.99/1.98    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f12,negated_conjecture,(
% 11.99/1.98    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 11.99/1.98    inference(negated_conjecture,[],[f11])).
% 11.99/1.98  
% 11.99/1.98  fof(f13,plain,(
% 11.99/1.98    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 11.99/1.98    inference(rectify,[],[f12])).
% 11.99/1.98  
% 11.99/1.98  fof(f15,plain,(
% 11.99/1.98    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 11.99/1.98    inference(pure_predicate_removal,[],[f13])).
% 11.99/1.98  
% 11.99/1.98  fof(f26,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.99/1.98    inference(ennf_transformation,[],[f15])).
% 11.99/1.98  
% 11.99/1.98  fof(f27,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.99/1.98    inference(flattening,[],[f26])).
% 11.99/1.98  
% 11.99/1.98  fof(f37,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.99/1.98    inference(nnf_transformation,[],[f27])).
% 11.99/1.98  
% 11.99/1.98  fof(f38,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.99/1.98    inference(flattening,[],[f37])).
% 11.99/1.98  
% 11.99/1.98  fof(f39,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.99/1.98    inference(rectify,[],[f38])).
% 11.99/1.98  
% 11.99/1.98  fof(f44,plain,(
% 11.99/1.98    ( ! [X0,X1] : (! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_yellow_0(X0,sK6(X5)) = X5 & r1_yellow_0(X0,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(X1)) & v1_finset_1(sK6(X5))))) )),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f43,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => ((~r2_lattice3(X0,X2,sK5) | ~r2_lattice3(X0,X1,sK5)) & (r2_lattice3(X0,X2,sK5) | r2_lattice3(X0,X1,sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f42,plain,(
% 11.99/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~r2_lattice3(X0,sK4,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,sK4,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f41,plain,(
% 11.99/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,sK3,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,sK3,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK3)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f40,plain,(
% 11.99/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK2,X2,X3) | ~r2_lattice3(sK2,X1,X3)) & (r2_lattice3(sK2,X2,X3) | r2_lattice3(sK2,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK2,X6) = X5 & r1_yellow_0(sK2,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f45,plain,(
% 11.99/1.98    ((((~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)) & (r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)) & m1_subset_1(sK5,u1_struct_0(sK2))) & ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK2,sK6(X5)) = X5 & r1_yellow_0(sK2,sK6(X5)) & m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) & v1_finset_1(sK6(X5))) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) & ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 11.99/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f39,f44,f43,f42,f41,f40])).
% 11.99/1.98  
% 11.99/1.98  fof(f69,plain,(
% 11.99/1.98    l1_orders_2(sK2)),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f7,axiom,(
% 11.99/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f20,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(ennf_transformation,[],[f7])).
% 11.99/1.98  
% 11.99/1.98  fof(f21,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(flattening,[],[f20])).
% 11.99/1.98  
% 11.99/1.98  fof(f28,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(nnf_transformation,[],[f21])).
% 11.99/1.98  
% 11.99/1.98  fof(f29,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(rectify,[],[f28])).
% 11.99/1.98  
% 11.99/1.98  fof(f30,plain,(
% 11.99/1.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 11.99/1.98    introduced(choice_axiom,[])).
% 11.99/1.98  
% 11.99/1.98  fof(f31,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 11.99/1.98  
% 11.99/1.98  fof(f54,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f31])).
% 11.99/1.98  
% 11.99/1.98  fof(f53,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f31])).
% 11.99/1.98  
% 11.99/1.98  fof(f3,axiom,(
% 11.99/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f16,plain,(
% 11.99/1.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.99/1.98    inference(ennf_transformation,[],[f3])).
% 11.99/1.98  
% 11.99/1.98  fof(f48,plain,(
% 11.99/1.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f16])).
% 11.99/1.98  
% 11.99/1.98  fof(f79,plain,(
% 11.99/1.98    r2_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK3,sK5)),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f4,axiom,(
% 11.99/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f14,plain,(
% 11.99/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 11.99/1.98    inference(unused_predicate_definition_removal,[],[f4])).
% 11.99/1.98  
% 11.99/1.98  fof(f17,plain,(
% 11.99/1.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.99/1.98    inference(ennf_transformation,[],[f14])).
% 11.99/1.98  
% 11.99/1.98  fof(f49,plain,(
% 11.99/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f17])).
% 11.99/1.98  
% 11.99/1.98  fof(f10,axiom,(
% 11.99/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f25,plain,(
% 11.99/1.98    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(ennf_transformation,[],[f10])).
% 11.99/1.98  
% 11.99/1.98  fof(f66,plain,(
% 11.99/1.98    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f25])).
% 11.99/1.98  
% 11.99/1.98  fof(f78,plain,(
% 11.99/1.98    m1_subset_1(sK5,u1_struct_0(sK2))),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f52,plain,(
% 11.99/1.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f31])).
% 11.99/1.98  
% 11.99/1.98  fof(f80,plain,(
% 11.99/1.98    ~r2_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK2,sK3,sK5)),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f55,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f31])).
% 11.99/1.98  
% 11.99/1.98  fof(f6,axiom,(
% 11.99/1.98    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f18,plain,(
% 11.99/1.98    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.99/1.98    inference(ennf_transformation,[],[f6])).
% 11.99/1.98  
% 11.99/1.98  fof(f19,plain,(
% 11.99/1.98    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.99/1.98    inference(flattening,[],[f18])).
% 11.99/1.98  
% 11.99/1.98  fof(f51,plain,(
% 11.99/1.98    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f19])).
% 11.99/1.98  
% 11.99/1.98  fof(f68,plain,(
% 11.99/1.98    v3_orders_2(sK2)),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f67,plain,(
% 11.99/1.98    ~v2_struct_0(sK2)),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f5,axiom,(
% 11.99/1.98    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f50,plain,(
% 11.99/1.98    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f5])).
% 11.99/1.98  
% 11.99/1.98  fof(f77,plain,(
% 11.99/1.98    ( ! [X4] : (r2_hidden(k1_yellow_0(sK2,X4),sK4) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK3)) | ~v1_finset_1(X4)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f72,plain,(
% 11.99/1.98    ( ! [X7] : (r1_yellow_0(sK2,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v1_finset_1(X7)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f9,axiom,(
% 11.99/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f24,plain,(
% 11.99/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.99/1.98    inference(ennf_transformation,[],[f9])).
% 11.99/1.98  
% 11.99/1.98  fof(f64,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f24])).
% 11.99/1.98  
% 11.99/1.98  fof(f59,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f36])).
% 11.99/1.98  
% 11.99/1.98  fof(f58,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f36])).
% 11.99/1.98  
% 11.99/1.98  fof(f60,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f36])).
% 11.99/1.98  
% 11.99/1.98  fof(f63,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f24])).
% 11.99/1.98  
% 11.99/1.98  fof(f1,axiom,(
% 11.99/1.98    v1_xboole_0(k1_xboole_0)),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f46,plain,(
% 11.99/1.98    v1_xboole_0(k1_xboole_0)),
% 11.99/1.98    inference(cnf_transformation,[],[f1])).
% 11.99/1.98  
% 11.99/1.98  fof(f2,axiom,(
% 11.99/1.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 11.99/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/1.98  
% 11.99/1.98  fof(f47,plain,(
% 11.99/1.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f2])).
% 11.99/1.98  
% 11.99/1.98  fof(f76,plain,(
% 11.99/1.98    ( ! [X5] : (k1_yellow_0(sK2,sK6(X5)) = X5 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f62,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f24])).
% 11.99/1.98  
% 11.99/1.98  fof(f65,plain,(
% 11.99/1.98    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f25])).
% 11.99/1.98  
% 11.99/1.98  fof(f61,plain,(
% 11.99/1.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.99/1.98    inference(cnf_transformation,[],[f24])).
% 11.99/1.98  
% 11.99/1.98  fof(f75,plain,(
% 11.99/1.98    ( ! [X5] : (r1_yellow_0(sK2,sK6(X5)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  fof(f74,plain,(
% 11.99/1.98    ( ! [X5] : (m1_subset_1(sK6(X5),k1_zfmisc_1(sK3)) | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 11.99/1.98    inference(cnf_transformation,[],[f45])).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2638,plain,
% 11.99/1.98      ( ~ r1_orders_2(X0_52,X0_53,X1_53)
% 11.99/1.98      | r1_orders_2(X0_52,X2_53,X3_53)
% 11.99/1.98      | X2_53 != X0_53
% 11.99/1.98      | X3_53 != X1_53 ),
% 11.99/1.98      theory(equality) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_30396,plain,
% 11.99/1.98      ( ~ r1_orders_2(sK2,X0_53,X1_53)
% 11.99/1.98      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.99/1.98      | sK0(sK2,sK4,sK5) != X0_53
% 11.99/1.98      | sK5 != X1_53 ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_2638]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_30678,plain,
% 11.99/1.98      ( ~ r1_orders_2(sK2,X0_53,sK5)
% 11.99/1.98      | r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.99/1.98      | sK0(sK2,sK4,sK5) != X0_53
% 11.99/1.98      | sK5 != sK5 ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_30396]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_31294,plain,
% 11.99/1.98      ( r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.99/1.98      | ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 11.99/1.98      | sK0(sK2,sK4,sK5) != k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.99/1.98      | sK5 != sK5 ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_30678]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_13,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 11.99/1.98      | ~ r1_yellow_0(X0,X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_32,negated_conjecture,
% 11.99/1.98      ( l1_orders_2(sK2) ),
% 11.99/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_715,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 11.99/1.98      | ~ r1_yellow_0(X0,X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 11.99/1.98      | sK2 != X0 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_716,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 11.99/1.98      | ~ r1_yellow_0(sK2,X0)
% 11.99/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_715]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2610,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,X0_53),X1_53)
% 11.99/1.98      | ~ r1_yellow_0(sK2,X0_53)
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,X0_53),u1_struct_0(sK2)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_716]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_18948,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,X0_53,sK5)),X1_53)
% 11.99/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),X1_53)
% 11.99/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),u1_struct_0(sK2)) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_2610]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_29158,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,X0_53,sK5)),sK5)
% 11.99/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),sK5)
% 11.99/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))),u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_18948]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_29160,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.99/1.98      | r1_orders_2(sK2,k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),sK5)
% 11.99/1.98      | ~ r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.99/1.98      | ~ m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_29158]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2633,plain,( X0_53 = X0_53 ),theory(equality) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_28703,plain,
% 11.99/1.98      ( sK0(sK2,X0_53,sK5) = sK0(sK2,X0_53,sK5) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_28704,plain,
% 11.99/1.98      ( sK0(sK2,sK4,sK5) = sK0(sK2,sK4,sK5) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_28703]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2636,plain,
% 11.99/1.98      ( ~ m1_subset_1(X0_53,X1_53)
% 11.99/1.98      | m1_subset_1(X2_53,X3_53)
% 11.99/1.98      | X2_53 != X0_53
% 11.99/1.98      | X3_53 != X1_53 ),
% 11.99/1.98      theory(equality) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3428,plain,
% 11.99/1.98      ( ~ m1_subset_1(X0_53,X1_53)
% 11.99/1.98      | m1_subset_1(X2_53,u1_struct_0(sK2))
% 11.99/1.98      | X2_53 != X0_53
% 11.99/1.98      | u1_struct_0(sK2) != X1_53 ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_2636]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3648,plain,
% 11.99/1.98      ( ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | X1_53 != X0_53
% 11.99/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_3428]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_19148,plain,
% 11.99/1.98      ( m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(sK0(sK2,X1_53,sK5),u1_struct_0(sK2))
% 11.99/1.98      | X0_53 != sK0(sK2,X1_53,sK5)
% 11.99/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_3648]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_28398,plain,
% 11.99/1.98      ( ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.99/1.98      | m1_subset_1(k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))),u1_struct_0(sK2))
% 11.99/1.98      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5)
% 11.99/1.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.99/1.98      inference(instantiation,[status(thm)],[c_19148]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_7,plain,
% 11.99/1.98      ( r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_835,plain,
% 11.99/1.98      ( r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | sK2 != X0 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_7,c_32]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_836,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0,X1)
% 11.99/1.98      | r2_hidden(sK0(sK2,X0,X1),X0)
% 11.99/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_835]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2604,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.98      | r2_hidden(sK0(sK2,X0_53,X1_53),X0_53)
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_836]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3344,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.98      | r2_hidden(sK0(sK2,X0_53,X1_53),X0_53) = iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2604]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_8,plain,
% 11.99/1.98      ( r2_lattice3(X0,X1,X2)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_820,plain,
% 11.99/1.98      ( r2_lattice3(X0,X1,X2)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 11.99/1.98      | sK2 != X0 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_32]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_821,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0,X1)
% 11.99/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.98      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_820]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2605,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | m1_subset_1(sK0(sK2,X0_53,X1_53),u1_struct_0(sK2)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_821]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3343,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.98      | m1_subset_1(sK0(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2605]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2,plain,
% 11.99/1.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 11.99/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2631,plain,
% 11.99/1.98      ( ~ r2_hidden(X0_53,X1_53)
% 11.99/1.98      | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(X1_53)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3318,plain,
% 11.99/1.98      ( r2_hidden(X0_53,X1_53) != iProver_top
% 11.99/1.98      | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(X1_53)) = iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2631]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_22,negated_conjecture,
% 11.99/1.98      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 11.99/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2629,negated_conjecture,
% 11.99/1.98      ( r2_lattice3(sK2,sK3,sK5) | r2_lattice3(sK2,sK4,sK5) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_22]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3320,plain,
% 11.99/1.98      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2629]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3,plain,
% 11.99/1.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.99/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_19,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_lattice3(X0,X3,X2)
% 11.99/1.98      | ~ r1_tarski(X3,X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(cnf_transformation,[],[f66]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_498,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_lattice3(X0,X3,X2)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.99/1.98      | ~ l1_orders_2(X0)
% 11.99/1.98      | X3 != X4
% 11.99/1.98      | X1 != X5 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_499,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_lattice3(X0,X3,X2)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_498]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_598,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r2_lattice3(X0,X3,X2)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.99/1.98      | sK2 != X0 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_499,c_32]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_599,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.98      | r2_lattice3(sK2,X2,X1)
% 11.99/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_598]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2617,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.98      | r2_lattice3(sK2,X2_53,X1_53)
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_599]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3331,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.98      | r2_lattice3(sK2,X2_53,X1_53) = iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.98      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2617]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3926,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top
% 11.99/1.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.98      inference(superposition,[status(thm)],[c_3320,c_3331]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_23,negated_conjecture,
% 11.99/1.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_58,plain,
% 11.99/1.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4041,plain,
% 11.99/1.98      ( m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.98      inference(global_propositional_subsumption,
% 11.99/1.98                [status(thm)],
% 11.99/1.98                [c_3926,c_58]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4042,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | m1_subset_1(X0_53,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.99/1.98      inference(renaming,[status(thm)],[c_4041]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4048,plain,
% 11.99/1.98      ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X0_53,sK3) != iProver_top ),
% 11.99/1.98      inference(superposition,[status(thm)],[c_3318,c_4042]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4056,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.98      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
% 11.99/1.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.98      inference(superposition,[status(thm)],[c_4048,c_3331]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4984,plain,
% 11.99/1.98      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
% 11.99/1.98      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.98      inference(global_propositional_subsumption,
% 11.99/1.98                [status(thm)],
% 11.99/1.98                [c_4056,c_58]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4985,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.98      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top ),
% 11.99/1.98      inference(renaming,[status(thm)],[c_4984]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4990,plain,
% 11.99/1.98      ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
% 11.99/1.98      | r2_hidden(X1_53,sK3) != iProver_top ),
% 11.99/1.98      inference(superposition,[status(thm)],[c_3318,c_4985]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_4993,plain,
% 11.99/1.98      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.98      inference(superposition,[status(thm)],[c_3344,c_4990]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_9,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r1_orders_2(X0,X3,X2)
% 11.99/1.98      | ~ r2_hidden(X3,X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.99/1.98      | ~ l1_orders_2(X0) ),
% 11.99/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_799,plain,
% 11.99/1.98      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.98      | r1_orders_2(X0,X3,X2)
% 11.99/1.98      | ~ r2_hidden(X3,X1)
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.99/1.98      | sK2 != X0 ),
% 11.99/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_32]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_800,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.98      | r1_orders_2(sK2,X2,X1)
% 11.99/1.98      | ~ r2_hidden(X2,X0)
% 11.99/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(unflattening,[status(thm)],[c_799]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_2606,plain,
% 11.99/1.98      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.98      | r1_orders_2(sK2,X2_53,X1_53)
% 11.99/1.98      | ~ r2_hidden(X2_53,X0_53)
% 11.99/1.98      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.98      | ~ m1_subset_1(X2_53,u1_struct_0(sK2)) ),
% 11.99/1.98      inference(subtyping,[status(esa)],[c_800]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_3342,plain,
% 11.99/1.98      ( r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.98      | r1_orders_2(sK2,X2_53,X1_53) = iProver_top
% 11.99/1.98      | r2_hidden(X2_53,X0_53) != iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.98      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.98      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 11.99/1.98  
% 11.99/1.98  cnf(c_6259,plain,
% 11.99/1.98      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.98      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.98      | r1_orders_2(sK2,X2_53,sK5) = iProver_top
% 11.99/1.98      | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
% 11.99/1.98      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.98      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.98      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_4993,c_3342]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11808,plain,
% 11.99/1.99      ( m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_6259,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11809,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_11808]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11814,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_11809]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_21,negated_conjecture,
% 11.99/1.99      ( ~ r2_lattice3(sK2,sK3,sK5) | ~ r2_lattice3(sK2,sK4,sK5) ),
% 11.99/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_60,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2652,plain,
% 11.99/1.99      ( sK4 = sK4 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6,plain,
% 11.99/1.99      ( r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_850,plain,
% 11.99/1.99      ( r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_851,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0,X1)
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0,X1),X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_850]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2603,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X1_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_851]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3443,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,X0_53,sK5),sK5)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2603]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3556,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3443]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3557,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3556]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3449,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,sK5),X0_53)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2604]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3582,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.99/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3449]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3583,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK3) = iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3582]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3437,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2605]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3595,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5)
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3437]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3596,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) = iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3595]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3411,plain,
% 11.99/1.99      ( ~ r2_hidden(X0_53,sK3)
% 11.99/1.99      | m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2631]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3693,plain,
% 11.99/1.99      ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK3)
% 11.99/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3411]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3694,plain,
% 11.99/1.99      ( r2_hidden(sK0(sK2,sK3,sK5),sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) = iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3693]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3490,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | r1_orders_2(sK2,X1_53,sK5)
% 11.99/1.99      | ~ r2_hidden(X1_53,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2606]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3696,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5)
% 11.99/1.99      | ~ r2_hidden(sK0(sK2,sK3,sK5),X0_53)
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3490]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3707,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,sK3,sK5),X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3696]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3709,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK4) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3707]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5,plain,
% 11.99/1.99      ( r1_orders_2(X0,X1,X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | v2_struct_0(X0)
% 11.99/1.99      | ~ v3_orders_2(X0)
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_33,negated_conjecture,
% 11.99/1.99      ( v3_orders_2(sK2) ),
% 11.99/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_458,plain,
% 11.99/1.99      ( r1_orders_2(X0,X1,X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | v2_struct_0(X0)
% 11.99/1.99      | ~ l1_orders_2(X0)
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_5,c_33]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_459,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0,X0)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | v2_struct_0(sK2)
% 11.99/1.99      | ~ l1_orders_2(sK2) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_458]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_34,negated_conjecture,
% 11.99/1.99      ( ~ v2_struct_0(sK2) ),
% 11.99/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_463,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_459,c_34,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2621,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_463]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3545,plain,
% 11.99/1.99      ( r1_orders_2(sK2,sK0(sK2,X0_53,sK5),sK0(sK2,X0_53,sK5))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2621]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3743,plain,
% 11.99/1.99      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3545]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3744,plain,
% 11.99/1.99      ( r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) = iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3743]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4,plain,
% 11.99/1.99      ( v1_finset_1(k1_tarski(X0)) ),
% 11.99/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24,negated_conjecture,
% 11.99/1.99      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 11.99/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.99/1.99      | ~ v1_finset_1(X0)
% 11.99/1.99      | k1_xboole_0 = X0 ),
% 11.99/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_544,plain,
% 11.99/1.99      ( r2_hidden(k1_yellow_0(sK2,X0),sK4)
% 11.99/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_tarski(X1) != X0
% 11.99/1.99      | k1_xboole_0 = X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_545,plain,
% 11.99/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0)),sK4)
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(X0) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_544]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2619,plain,
% 11.99/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(X0_53)),sK4)
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(X0_53) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_545]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3939,plain,
% 11.99/1.99      ( r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2619]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3940,plain,
% 11.99/1.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 11.99/1.99      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) = iProver_top
% 11.99/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3939]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_29,negated_conjecture,
% 11.99/1.99      ( r1_yellow_0(sK2,X0)
% 11.99/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.99/1.99      | ~ v1_finset_1(X0)
% 11.99/1.99      | k1_xboole_0 = X0 ),
% 11.99/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_529,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,X0)
% 11.99/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_tarski(X1) != X0
% 11.99/1.99      | k1_xboole_0 = X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_29]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_530,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,k1_tarski(X0))
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(X0) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_529]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2620,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,k1_tarski(X0_53))
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(X0_53),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(X0_53) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_530]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3938,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3))
% 11.99/1.99      | k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2620]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3942,plain,
% 11.99/1.99      ( k1_xboole_0 = k1_tarski(sK0(sK2,sK3,sK5))
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = iProver_top
% 11.99/1.99      | m1_subset_1(k1_tarski(sK0(sK2,sK3,sK5)),k1_zfmisc_1(sK3)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3938]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_15,plain,
% 11.99/1.99      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_682,plain,
% 11.99/1.99      ( r2_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_683,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0),X1)
% 11.99/1.99      | ~ r1_orders_2(sK2,X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_682]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2612,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53)
% 11.99/1.99      | ~ r1_orders_2(sK2,X0_53,X1_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_683]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3505,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),sK0(sK2,X1_53,sK5))
% 11.99/1.99      | ~ r1_orders_2(sK2,X0_53,sK0(sK2,X1_53,sK5))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,X1_53,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3716,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,X0_53,sK5))
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,X0_53,sK5))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,X0_53,sK5),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3505]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3975,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3716]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3976,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK0(sK2,sK3,sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_3975]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6123,plain,
% 11.99/1.99      ( sK0(sK2,sK3,sK5) = sK0(sK2,sK3,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6567,plain,
% 11.99/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) = k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0)
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.99/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_757,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_758,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.99      | r2_lattice3(sK2,X0,sK1(sK2,X0,X1))
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_757]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2608,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK1(sK2,X0_53,X1_53))
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = X1_53 ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_758]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5874,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53))
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2608]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6689,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5874]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6690,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_6689]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_12,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0)
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.99/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_736,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_737,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_736]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2609,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = X1_53 ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_737]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5875,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2609]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6702,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5875]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6703,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.99/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) = iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_6702]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_10,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0)
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2 ),
% 11.99/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_778,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,X1,X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 11.99/1.99      | ~ r1_yellow_0(X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | k1_yellow_0(X0,X1) = X2
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_779,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0,X1)
% 11.99/1.99      | ~ r1_orders_2(sK2,X1,sK1(sK2,X0,X1))
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0) = X1 ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_778]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2607,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,X1_53)
% 11.99/1.99      | ~ r1_orders_2(sK2,X1_53,sK1(sK2,X0_53,X1_53))
% 11.99/1.99      | ~ r1_yellow_0(sK2,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = X1_53 ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_779]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5873,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53)
% 11.99/1.99      | ~ r1_orders_2(sK2,X0_53,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),X0_53))
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = X0_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2607]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6717,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5873]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6718,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) = sK0(sK2,sK3,sK5)
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_6717]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2634,plain,
% 11.99/1.99      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 11.99/1.99      theory(equality) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4458,plain,
% 11.99/1.99      ( X0_53 != X1_53
% 11.99/1.99      | sK0(sK2,X2_53,sK5) != X1_53
% 11.99/1.99      | sK0(sK2,X2_53,sK5) = X0_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2634]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5326,plain,
% 11.99/1.99      ( X0_53 != sK0(sK2,X1_53,sK5)
% 11.99/1.99      | sK0(sK2,X1_53,sK5) = X0_53
% 11.99/1.99      | sK0(sK2,X1_53,sK5) != sK0(sK2,X1_53,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_4458]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_7768,plain,
% 11.99/1.99      ( sK0(sK2,sK3,sK5) != sK0(sK2,sK3,sK5)
% 11.99/1.99      | sK0(sK2,sK3,sK5) = k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))) != sK0(sK2,sK3,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5326]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4849,plain,
% 11.99/1.99      ( X0_53 != X1_53
% 11.99/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) != X1_53
% 11.99/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2634]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_7657,plain,
% 11.99/1.99      ( X0_53 != k1_tarski(sK0(sK2,sK3,sK5))
% 11.99/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = X0_53
% 11.99/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_4849]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8419,plain,
% 11.99/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_tarski(sK0(sK2,sK3,sK5))
% 11.99/1.99      | k1_tarski(sK0(sK2,sK3,sK5)) = k1_xboole_0
% 11.99/1.99      | k1_xboole_0 != k1_tarski(sK0(sK2,sK3,sK5)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_7657]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6260,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_4993,c_3331]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8543,plain,
% 11.99/1.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_6260,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8544,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X1_53),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(sK0(sK2,k1_tarski(X1_53),X2_53)))) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_8543]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8549,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X2_53,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53))) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3318,c_8544]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8719,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53)),sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_8549]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_16,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | r1_orders_2(X0,X1,X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_666,plain,
% 11.99/1.99      ( ~ r2_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | r1_orders_2(X0,X1,X2)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_667,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0),X1)
% 11.99/1.99      | r1_orders_2(sK2,X0,X1)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_666]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2613,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0_53),X1_53)
% 11.99/1.99      | r1_orders_2(sK2,X0_53,X1_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_667]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3335,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2613]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11131,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_8719,c_3335]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2637,plain,
% 11.99/1.99      ( ~ r2_hidden(X0_53,X1_53)
% 11.99/1.99      | r2_hidden(X2_53,X3_53)
% 11.99/1.99      | X2_53 != X0_53
% 11.99/1.99      | X3_53 != X1_53 ),
% 11.99/1.99      theory(equality) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3406,plain,
% 11.99/1.99      ( ~ r2_hidden(X0_53,X1_53)
% 11.99/1.99      | r2_hidden(X2_53,sK4)
% 11.99/1.99      | X2_53 != X0_53
% 11.99/1.99      | sK4 != X1_53 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2637]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5913,plain,
% 11.99/1.99      ( r2_hidden(X0_53,sK4)
% 11.99/1.99      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.99/1.99      | X0_53 != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | sK4 != sK4 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3406]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11473,plain,
% 11.99/1.99      ( r2_hidden(sK0(sK2,sK3,sK5),sK4)
% 11.99/1.99      | ~ r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4)
% 11.99/1.99      | sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | sK4 != sK4 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5913]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_11474,plain,
% 11.99/1.99      ( sK0(sK2,sK3,sK5) != k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5)))
% 11.99/1.99      | sK4 != sK4
% 11.99/1.99      | r2_hidden(sK0(sK2,sK3,sK5),sK4) = iProver_top
% 11.99/1.99      | r2_hidden(k1_yellow_0(sK2,k1_tarski(sK0(sK2,sK3,sK5))),sK4) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_11473]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_0,plain,
% 11.99/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_1,plain,
% 11.99/1.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 11.99/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_452,plain,
% 11.99/1.99      ( k1_tarski(X0) != k1_xboole_0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2622,plain,
% 11.99/1.99      ( k1_tarski(X0_53) != k1_xboole_0 ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_452]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_13889,plain,
% 11.99/1.99      ( k1_tarski(sK0(sK2,sK3,sK5)) != k1_xboole_0 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2622]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_10122,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(X0_53),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | r1_orders_2(sK2,X0_53,sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2613]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_17752,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)))
% 11.99/1.99      | ~ m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_10122]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_17753,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,sK3,sK5),sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5))) = iProver_top
% 11.99/1.99      | m1_subset_1(sK1(sK2,k1_tarski(sK0(sK2,sK3,sK5)),sK0(sK2,sK3,sK5)),u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK3,sK5),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_17752]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24418,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_11814,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,
% 11.99/1.99                 c_3709,c_3744,c_3940,c_3942,c_3976,c_6123,c_6567,c_6690,
% 11.99/1.99                 c_6703,c_6718,c_7768,c_8419,c_11131,c_11474,c_13889,
% 11.99/1.99                 c_17753]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24419,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_24418]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24424,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),X2_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_24419]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3345,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X1_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2603]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24476,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_24424,c_3345]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24506,plain,
% 11.99/1.99      ( m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_24476,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24507,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK0(sK2,k1_tarski(X0_53),X1_53)),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_24506]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24517,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(X0_53),X1_53),u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_24507,c_3335]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4261,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_4048,c_3342]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6640,plain,
% 11.99/1.99      ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_4261,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6641,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
% 11.99/1.99      | r2_hidden(X1_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_6640]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_6645,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X2_53,sK3) != iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,X1_53),k1_tarski(X2_53)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_6641]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_7130,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_6645]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24656,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(X0_53),X1_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_24517,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,
% 11.99/1.99                 c_3709,c_3744,c_3940,c_3942,c_3976,c_6123,c_6567,c_6690,
% 11.99/1.99                 c_6703,c_6718,c_7130,c_7768,c_8419,c_11474,c_13889,
% 11.99/1.99                 c_17753]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24662,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_24656,c_3345]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24780,plain,
% 11.99/1.99      ( r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_24662,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,
% 11.99/1.99                 c_3709,c_3744,c_3940,c_3942,c_3976,c_4048,c_6123,c_6567,
% 11.99/1.99                 c_6690,c_6703,c_6718,c_7768,c_8419,c_11474,c_13889,
% 11.99/1.99                 c_17753]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24781,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_24780]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24791,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_24781,c_3335]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24807,plain,
% 11.99/1.99      ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_24791,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24808,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_24807]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_24814,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,X1_53),sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_24808]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25403,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_24814,c_3345]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25422,plain,
% 11.99/1.99      ( r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_25403,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25423,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,sK5),sK3) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_25422]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25426,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) = iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_25423]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25427,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK3,sK5) | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_25426]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2628,negated_conjecture,
% 11.99/1.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_23]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3321,plain,
% 11.99/1.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_25,negated_conjecture,
% 11.99/1.99      ( ~ r2_hidden(X0,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,sK6(X0)) = X0 ),
% 11.99/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2627,negated_conjecture,
% 11.99/1.99      ( ~ r2_hidden(X0_53,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | k1_yellow_0(sK2,sK6(X0_53)) = X0_53 ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_25]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3322,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,sK6(X0_53)) = X0_53
% 11.99/1.99      | r2_hidden(X0_53,sK4) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4506,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,X1_53))) = sK0(sK2,X0_53,X1_53)
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,X1_53),sK4) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_3322]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4658,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,X0_53))) = sK0(sK2,sK4,X0_53)
% 11.99/1.99      | r2_lattice3(sK2,sK4,X0_53) = iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_4506]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4663,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 11.99/1.99      | r2_lattice3(sK2,sK4,sK5) = iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3321,c_4658]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3339,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3336,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2612]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4260,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,X1_53) = iProver_top
% 11.99/1.99      | r2_hidden(X2_53,k1_tarski(X0_53)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3336,c_3342]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4880,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3321,c_4260]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5062,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,X0_53,X1_53),X2_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X2_53) != iProver_top
% 11.99/1.99      | r2_hidden(sK0(sK2,X0_53,X1_53),k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_4880]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_7185,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK0(sK2,k1_tarski(sK5),X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_5062]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_7287,plain,
% 11.99/1.99      ( r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_7185,c_3345]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3340,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK1(sK2,X0_53,X1_53)) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2608]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4784,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r2_hidden(X2_53,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3340,c_3342]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2699,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK1(sK2,X0_53,X1_53),u1_struct_0(sK2)) = iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8626,plain,
% 11.99/1.99      ( m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r2_hidden(X2_53,X0_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = X1_53 ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_4784,c_2699]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8627,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X2_53,sK1(sK2,X0_53,X1_53)) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r2_hidden(X2_53,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_8626]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3341,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X1_53,sK1(sK2,X0_53,X1_53)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2607]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8634,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r2_hidden(X1_53,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_8627,c_3341]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_8827,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,k1_tarski(sK5)) = X0_53
% 11.99/1.99      | r1_orders_2(sK2,sK5,X0_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_7287,c_8634]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3327,plain,
% 11.99/1.99      ( r1_orders_2(sK2,X0_53,X0_53) = iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3819,plain,
% 11.99/1.99      ( r1_orders_2(sK2,sK5,sK5) = iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3321,c_3327]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_17,plain,
% 11.99/1.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X2,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_648,plain,
% 11.99/1.99      ( r1_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | ~ r1_orders_2(X0,X2,X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_649,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0),X1)
% 11.99/1.99      | ~ r1_orders_2(sK2,X1,X0)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_648]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2614,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53)
% 11.99/1.99      | ~ r1_orders_2(sK2,X1_53,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_649]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3334,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X1_53,X0_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2614]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_20,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.99/1.99      | r1_lattice3(X0,X3,X2)
% 11.99/1.99      | ~ r1_tarski(X3,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_479,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.99/1.99      | r1_lattice3(X0,X3,X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.99/1.99      | ~ l1_orders_2(X0)
% 11.99/1.99      | X3 != X4
% 11.99/1.99      | X1 != X5 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_480,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.99/1.99      | r1_lattice3(X0,X3,X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_479]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_614,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,X1,X2)
% 11.99/1.99      | r1_lattice3(X0,X3,X2)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_480,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_615,plain,
% 11.99/1.99      ( ~ r1_lattice3(sK2,X0,X1)
% 11.99/1.99      | r1_lattice3(sK2,X2,X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_614]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2616,plain,
% 11.99/1.99      ( ~ r1_lattice3(sK2,X0_53,X1_53)
% 11.99/1.99      | r1_lattice3(sK2,X2_53,X1_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_615]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3332,plain,
% 11.99/1.99      ( r1_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_lattice3(sK2,X2_53,X1_53) = iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2616]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3931,plain,
% 11.99/1.99      ( r1_lattice3(sK2,X0_53,sK5) != iProver_top
% 11.99/1.99      | r1_lattice3(sK2,X1_53,sK5) = iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3321,c_3332]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4098,plain,
% 11.99/1.99      ( r1_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3334,c_3931]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4852,plain,
% 11.99/1.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | r1_lattice3(sK2,X0_53,sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_4098,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4853,plain,
% 11.99/1.99      ( r1_lattice3(sK2,X0_53,sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,k1_zfmisc_1(k1_tarski(X1_53))) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_4852]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4858,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X1_53) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(X1_53)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3318,c_4853]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5056,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3819,c_4858]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5153,plain,
% 11.99/1.99      ( r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_5056,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5154,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),sK5) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_5153]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_18,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | r1_orders_2(X0,X2,X1)
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ l1_orders_2(X0) ),
% 11.99/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_630,plain,
% 11.99/1.99      ( ~ r1_lattice3(X0,k1_tarski(X1),X2)
% 11.99/1.99      | r1_orders_2(X0,X2,X1)
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.99/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.99/1.99      | sK2 != X0 ),
% 11.99/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_631,plain,
% 11.99/1.99      ( ~ r1_lattice3(sK2,k1_tarski(X0),X1)
% 11.99/1.99      | r1_orders_2(sK2,X1,X0)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(unflattening,[status(thm)],[c_630]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2615,plain,
% 11.99/1.99      ( ~ r1_lattice3(sK2,k1_tarski(X0_53),X1_53)
% 11.99/1.99      | r1_orders_2(sK2,X1_53,X0_53)
% 11.99/1.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_631]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3333,plain,
% 11.99/1.99      ( r1_lattice3(sK2,k1_tarski(X0_53),X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,X1_53,X0_53) = iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(predicate_to_equality,[status(thm)],[c_2615]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_5159,plain,
% 11.99/1.99      ( r1_orders_2(sK2,sK5,X0_53) = iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_5154,c_3333]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_21983,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,k1_tarski(sK5)) = X0_53
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r2_hidden(X0_53,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_8827,c_58,c_5159]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_21989,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK0(sK2,k1_tarski(sK5),X0_53),u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3344,c_21983]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22193,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | r2_lattice3(sK2,k1_tarski(sK5),X0_53) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3343,c_21989]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22202,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | r1_orders_2(sK2,sK5,X0_53) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_22193,c_3335]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22256,plain,
% 11.99/1.99      ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,X0_53) = iProver_top
% 11.99/1.99      | sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_22202,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22257,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),X0_53) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | r1_orders_2(sK2,sK5,X0_53) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_22256]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22264,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,X1_53)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = X1_53
% 11.99/1.99      | r2_lattice3(sK2,X0_53,X1_53) != iProver_top
% 11.99/1.99      | r1_orders_2(sK2,sK5,sK1(sK2,X0_53,X1_53)) = iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(X1_53,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_3339,c_22257]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22417,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = sK5
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK5) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_22264,c_3341]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22441,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK5) != iProver_top
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = sK5
% 11.99/1.99      | sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5)) ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_22417,c_58]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22442,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,X0_53,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | k1_yellow_0(sK2,X0_53) = sK5
% 11.99/1.99      | r2_lattice3(sK2,X0_53,sK5) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,X0_53) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top ),
% 11.99/1.99      inference(renaming,[status(thm)],[c_22441]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22447,plain,
% 11.99/1.99      ( sK0(sK2,k1_tarski(sK5),sK1(sK2,sK4,sK5)) = k1_yellow_0(sK2,k1_tarski(sK5))
% 11.99/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5)
% 11.99/1.99      | k1_yellow_0(sK2,sK4) = sK5
% 11.99/1.99      | r1_yellow_0(sK2,k1_tarski(sK5)) != iProver_top
% 11.99/1.99      | r1_yellow_0(sK2,sK4) != iProver_top ),
% 11.99/1.99      inference(superposition,[status(thm)],[c_4663,c_22442]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_22702,plain,
% 11.99/1.99      ( k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) = sK0(sK2,sK4,sK5) ),
% 11.99/1.99      inference(global_propositional_subsumption,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_22447,c_58,c_60,c_2652,c_3557,c_3583,c_3596,c_3694,
% 11.99/1.99                 c_3709,c_3744,c_3940,c_3942,c_3976,c_4663,c_6123,c_6567,
% 11.99/1.99                 c_6690,c_6703,c_6718,c_7768,c_8419,c_11474,c_13889,
% 11.99/1.99                 c_17753]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3486,plain,
% 11.99/1.99      ( ~ r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | r2_lattice3(sK2,X1_53,sK5)
% 11.99/1.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X0_53))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2617]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3859,plain,
% 11.99/1.99      ( r2_lattice3(sK2,X0_53,sK5)
% 11.99/1.99      | ~ r2_lattice3(sK2,sK3,sK5)
% 11.99/1.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(sK3))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3486]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_19220,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK6(sK0(sK2,sK4,sK5)),sK5)
% 11.99/1.99      | ~ r2_lattice3(sK2,sK3,sK5)
% 11.99/1.99      | ~ m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3859]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_19016,plain,
% 11.99/1.99      ( sK0(sK2,X0_53,sK5) != sK0(sK2,X0_53,sK5)
% 11.99/1.99      | sK0(sK2,X0_53,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5)))
% 11.99/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,X0_53,sK5))) != sK0(sK2,X0_53,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_5326]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_19028,plain,
% 11.99/1.99      ( sK0(sK2,sK4,sK5) != sK0(sK2,sK4,sK5)
% 11.99/1.99      | sK0(sK2,sK4,sK5) = k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.99/1.99      | k1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5))) != sK0(sK2,sK4,sK5) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_19016]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_4397,plain,
% 11.99/1.99      ( sK5 = sK5 ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3989,plain,
% 11.99/1.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2633]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_26,negated_conjecture,
% 11.99/1.99      ( r1_yellow_0(sK2,sK6(X0))
% 11.99/1.99      | ~ r2_hidden(X0,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2626,negated_conjecture,
% 11.99/1.99      ( r1_yellow_0(sK2,sK6(X0_53))
% 11.99/1.99      | ~ r2_hidden(X0_53,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_26]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3825,plain,
% 11.99/1.99      ( r1_yellow_0(sK2,sK6(sK0(sK2,sK4,sK5)))
% 11.99/1.99      | ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2626]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_27,negated_conjecture,
% 11.99/1.99      ( ~ r2_hidden(X0,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK6(X0),k1_zfmisc_1(sK3)) ),
% 11.99/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_2625,negated_conjecture,
% 11.99/1.99      ( ~ r2_hidden(X0_53,sK4)
% 11.99/1.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK6(X0_53),k1_zfmisc_1(sK3)) ),
% 11.99/1.99      inference(subtyping,[status(esa)],[c_27]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3826,plain,
% 11.99/1.99      ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.99/1.99      | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.99/1.99      | m1_subset_1(sK6(sK0(sK2,sK4,sK5)),k1_zfmisc_1(sK3)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_2625]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3451,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.99/1.99      | r2_hidden(sK0(sK2,sK4,sK5),sK4)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3449]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3445,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.99/1.99      | ~ r1_orders_2(sK2,sK0(sK2,sK4,sK5),sK5)
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3443]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(c_3439,plain,
% 11.99/1.99      ( r2_lattice3(sK2,sK4,sK5)
% 11.99/1.99      | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
% 11.99/1.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 11.99/1.99      inference(instantiation,[status(thm)],[c_3437]) ).
% 11.99/1.99  
% 11.99/1.99  cnf(contradiction,plain,
% 11.99/1.99      ( $false ),
% 11.99/1.99      inference(minisat,
% 11.99/1.99                [status(thm)],
% 11.99/1.99                [c_31294,c_29160,c_28704,c_28398,c_25427,c_22702,c_19220,
% 11.99/1.99                 c_19028,c_4397,c_3989,c_3825,c_3826,c_3451,c_3445,
% 11.99/1.99                 c_3439,c_21,c_23]) ).
% 11.99/1.99  
% 11.99/1.99  
% 11.99/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.99/1.99  
% 11.99/1.99  ------                               Statistics
% 11.99/1.99  
% 11.99/1.99  ------ General
% 11.99/1.99  
% 11.99/1.99  abstr_ref_over_cycles:                  0
% 11.99/1.99  abstr_ref_under_cycles:                 0
% 11.99/1.99  gc_basic_clause_elim:                   0
% 11.99/1.99  forced_gc_time:                         0
% 11.99/1.99  parsing_time:                           0.011
% 11.99/1.99  unif_index_cands_time:                  0.
% 11.99/1.99  unif_index_add_time:                    0.
% 11.99/1.99  orderings_time:                         0.
% 11.99/1.99  out_proof_time:                         0.025
% 11.99/1.99  total_time:                             1.306
% 11.99/1.99  num_of_symbols:                         54
% 11.99/1.99  num_of_terms:                           21290
% 11.99/1.99  
% 11.99/1.99  ------ Preprocessing
% 11.99/1.99  
% 11.99/1.99  num_of_splits:                          0
% 11.99/1.99  num_of_split_atoms:                     0
% 11.99/1.99  num_of_reused_defs:                     0
% 11.99/1.99  num_eq_ax_congr_red:                    35
% 11.99/1.99  num_of_sem_filtered_clauses:            1
% 11.99/1.99  num_of_subtypes:                        2
% 11.99/1.99  monotx_restored_types:                  0
% 11.99/1.99  sat_num_of_epr_types:                   0
% 11.99/1.99  sat_num_of_non_cyclic_types:            0
% 11.99/1.99  sat_guarded_non_collapsed_types:        1
% 11.99/1.99  num_pure_diseq_elim:                    0
% 11.99/1.99  simp_replaced_by:                       0
% 11.99/1.99  res_preprocessed:                       143
% 11.99/1.99  prep_upred:                             0
% 11.99/1.99  prep_unflattend:                        110
% 11.99/1.99  smt_new_axioms:                         0
% 11.99/1.99  pred_elim_cands:                        6
% 11.99/1.99  pred_elim:                              6
% 11.99/1.99  pred_elim_cl:                           6
% 11.99/1.99  pred_elim_cycles:                       10
% 11.99/1.99  merged_defs:                            8
% 11.99/1.99  merged_defs_ncl:                        0
% 11.99/1.99  bin_hyper_res:                          8
% 11.99/1.99  prep_cycles:                            4
% 11.99/1.99  pred_elim_time:                         0.037
% 11.99/1.99  splitting_time:                         0.
% 11.99/1.99  sem_filter_time:                        0.
% 11.99/1.99  monotx_time:                            0.
% 11.99/1.99  subtype_inf_time:                       0.
% 11.99/1.99  
% 11.99/1.99  ------ Problem properties
% 11.99/1.99  
% 11.99/1.99  clauses:                                29
% 11.99/1.99  conjectures:                            8
% 11.99/1.99  epr:                                    2
% 11.99/1.99  horn:                                   21
% 11.99/1.99  ground:                                 5
% 11.99/1.99  unary:                                  4
% 11.99/1.99  binary:                                 4
% 11.99/1.99  lits:                                   92
% 11.99/1.99  lits_eq:                                8
% 11.99/1.99  fd_pure:                                0
% 11.99/1.99  fd_pseudo:                              0
% 11.99/1.99  fd_cond:                                0
% 11.99/1.99  fd_pseudo_cond:                         3
% 11.99/1.99  ac_symbols:                             0
% 11.99/1.99  
% 11.99/1.99  ------ Propositional Solver
% 11.99/1.99  
% 11.99/1.99  prop_solver_calls:                      43
% 11.99/1.99  prop_fast_solver_calls:                 6626
% 11.99/1.99  smt_solver_calls:                       0
% 11.99/1.99  smt_fast_solver_calls:                  0
% 11.99/1.99  prop_num_of_clauses:                    14927
% 11.99/1.99  prop_preprocess_simplified:             21160
% 11.99/1.99  prop_fo_subsumed:                       299
% 11.99/1.99  prop_solver_time:                       0.
% 11.99/1.99  smt_solver_time:                        0.
% 11.99/1.99  smt_fast_solver_time:                   0.
% 11.99/1.99  prop_fast_solver_time:                  0.
% 11.99/1.99  prop_unsat_core_time:                   0.001
% 11.99/1.99  
% 11.99/1.99  ------ QBF
% 11.99/1.99  
% 11.99/1.99  qbf_q_res:                              0
% 11.99/1.99  qbf_num_tautologies:                    0
% 11.99/1.99  qbf_prep_cycles:                        0
% 11.99/1.99  
% 11.99/1.99  ------ BMC1
% 11.99/1.99  
% 11.99/1.99  bmc1_current_bound:                     -1
% 11.99/1.99  bmc1_last_solved_bound:                 -1
% 11.99/1.99  bmc1_unsat_core_size:                   -1
% 11.99/1.99  bmc1_unsat_core_parents_size:           -1
% 11.99/1.99  bmc1_merge_next_fun:                    0
% 11.99/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.99/1.99  
% 11.99/1.99  ------ Instantiation
% 11.99/1.99  
% 11.99/1.99  inst_num_of_clauses:                    201
% 11.99/1.99  inst_num_in_passive:                    80
% 11.99/1.99  inst_num_in_active:                     2451
% 11.99/1.99  inst_num_in_unprocessed:                1
% 11.99/1.99  inst_num_of_loops:                      3123
% 11.99/1.99  inst_num_of_learning_restarts:          1
% 11.99/1.99  inst_num_moves_active_passive:          658
% 11.99/1.99  inst_lit_activity:                      0
% 11.99/1.99  inst_lit_activity_moves:                1
% 11.99/1.99  inst_num_tautologies:                   0
% 11.99/1.99  inst_num_prop_implied:                  0
% 11.99/1.99  inst_num_existing_simplified:           0
% 11.99/1.99  inst_num_eq_res_simplified:             0
% 11.99/1.99  inst_num_child_elim:                    0
% 11.99/1.99  inst_num_of_dismatching_blockings:      2260
% 11.99/1.99  inst_num_of_non_proper_insts:           5783
% 11.99/1.99  inst_num_of_duplicates:                 0
% 11.99/1.99  inst_inst_num_from_inst_to_res:         0
% 11.99/1.99  inst_dismatching_checking_time:         0.
% 11.99/1.99  
% 11.99/1.99  ------ Resolution
% 11.99/1.99  
% 11.99/1.99  res_num_of_clauses:                     39
% 11.99/1.99  res_num_in_passive:                     39
% 11.99/1.99  res_num_in_active:                      0
% 11.99/1.99  res_num_of_loops:                       147
% 11.99/1.99  res_forward_subset_subsumed:            193
% 11.99/1.99  res_backward_subset_subsumed:           0
% 11.99/1.99  res_forward_subsumed:                   0
% 11.99/1.99  res_backward_subsumed:                  0
% 11.99/1.99  res_forward_subsumption_resolution:     3
% 11.99/1.99  res_backward_subsumption_resolution:    0
% 11.99/1.99  res_clause_to_clause_subsumption:       9731
% 11.99/1.99  res_orphan_elimination:                 0
% 11.99/1.99  res_tautology_del:                      487
% 11.99/1.99  res_num_eq_res_simplified:              0
% 11.99/1.99  res_num_sel_changes:                    0
% 11.99/1.99  res_moves_from_active_to_pass:          0
% 11.99/1.99  
% 11.99/1.99  ------ Superposition
% 11.99/1.99  
% 11.99/1.99  sup_time_total:                         0.
% 11.99/1.99  sup_time_generating:                    0.
% 11.99/1.99  sup_time_sim_full:                      0.
% 11.99/1.99  sup_time_sim_immed:                     0.
% 11.99/1.99  
% 11.99/1.99  sup_num_of_clauses:                     1169
% 11.99/1.99  sup_num_in_active:                      463
% 11.99/1.99  sup_num_in_passive:                     706
% 11.99/1.99  sup_num_of_loops:                       624
% 11.99/1.99  sup_fw_superposition:                   863
% 11.99/1.99  sup_bw_superposition:                   827
% 11.99/1.99  sup_immediate_simplified:               275
% 11.99/1.99  sup_given_eliminated:                   0
% 11.99/1.99  comparisons_done:                       0
% 11.99/1.99  comparisons_avoided:                    275
% 11.99/1.99  
% 11.99/1.99  ------ Simplifications
% 11.99/1.99  
% 11.99/1.99  
% 11.99/1.99  sim_fw_subset_subsumed:                 123
% 11.99/1.99  sim_bw_subset_subsumed:                 185
% 11.99/1.99  sim_fw_subsumed:                        95
% 11.99/1.99  sim_bw_subsumed:                        90
% 11.99/1.99  sim_fw_subsumption_res:                 0
% 11.99/1.99  sim_bw_subsumption_res:                 0
% 11.99/1.99  sim_tautology_del:                      7
% 11.99/1.99  sim_eq_tautology_del:                   2
% 11.99/1.99  sim_eq_res_simp:                        0
% 11.99/1.99  sim_fw_demodulated:                     1
% 11.99/1.99  sim_bw_demodulated:                     3
% 11.99/1.99  sim_light_normalised:                   2
% 11.99/1.99  sim_joinable_taut:                      0
% 11.99/1.99  sim_joinable_simp:                      0
% 11.99/1.99  sim_ac_normalised:                      0
% 11.99/1.99  sim_smt_subsumption:                    0
% 11.99/1.99  
%------------------------------------------------------------------------------
