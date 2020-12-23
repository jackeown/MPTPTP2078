%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1678+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:10 EST 2020

% Result     : Theorem 27.80s
% Output     : CNFRefutation 27.80s
% Verified   : 
% Statistics : Number of formulae       :  278 (1676 expanded)
%              Number of clauses        :  209 ( 455 expanded)
%              Number of leaves         :   14 ( 414 expanded)
%              Depth                    :   29
%              Number of atoms          : 2406 (23589 expanded)
%              Number of equality atoms :  929 (3732 expanded)
%              Maximal formula depth    :   21 (   9 average)
%              Maximal clause size      :   48 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
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
    inference(rectify,[],[f2])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
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
    inference(definition_folding,[],[f10,f14,f13])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f3,conjecture,(
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
               => ( r2_yellow_0(X0,X1)
                <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
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
                 => ( r2_yellow_0(X0,X1)
                  <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
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
                 => ( r2_yellow_0(X0,X1)
                  <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_yellow_0(X0,X1)
              <~> r2_yellow_0(X0,X2) )
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
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_yellow_0(X0,X1)
              <~> r2_yellow_0(X0,X2) )
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
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X0,X2)
                | ~ r2_yellow_0(X0,X1) )
              & ( r2_yellow_0(X0,X2)
                | r2_yellow_0(X0,X1) )
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
    inference(nnf_transformation,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X0,X2)
                | ~ r2_yellow_0(X0,X1) )
              & ( r2_yellow_0(X0,X2)
                | r2_yellow_0(X0,X1) )
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_yellow_0(X0,X2)
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X2)
            | r2_yellow_0(X0,X1) )
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
     => ( ( ~ r2_yellow_0(X0,sK8)
          | ~ r2_yellow_0(X0,X1) )
        & ( r2_yellow_0(X0,sK8)
          | r2_yellow_0(X0,X1) )
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

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X0,X2)
                | ~ r2_yellow_0(X0,X1) )
              & ( r2_yellow_0(X0,X2)
                | r2_yellow_0(X0,X1) )
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
            ( ( ~ r2_yellow_0(X0,X2)
              | ~ r2_yellow_0(X0,sK7) )
            & ( r2_yellow_0(X0,X2)
              | r2_yellow_0(X0,sK7) )
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

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_yellow_0(X0,X2)
                  | ~ r2_yellow_0(X0,X1) )
                & ( r2_yellow_0(X0,X2)
                  | r2_yellow_0(X0,X1) )
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
              ( ( ~ r2_yellow_0(sK6,X2)
                | ~ r2_yellow_0(sK6,X1) )
              & ( r2_yellow_0(sK6,X2)
                | r2_yellow_0(sK6,X1) )
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

fof(f38,plain,
    ( ( ~ r2_yellow_0(sK6,sK8)
      | ~ r2_yellow_0(sK6,sK7) )
    & ( r2_yellow_0(sK6,sK8)
      | r2_yellow_0(sK6,sK7) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f37,f36,f35,f34])).

fof(f60,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4] :
      ( k2_yellow_0(sK6,sK9(X4)) = X4
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( r2_yellow_0(sK6,sK8)
    | r2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK4(X0,X1))
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X6] :
      ( r2_yellow_0(sK6,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0)
        & k1_xboole_0 != sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK6,X3),sK8)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK3(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( ~ r2_yellow_0(sK6,sK8)
    | ~ r2_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X4] :
      ( m1_subset_1(sK9(X4),k1_zfmisc_1(sK7))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X4] :
      ( r2_yellow_0(sK6,sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X4] :
      ( v1_finset_1(sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_353,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X1_52,X2_52)
    | r1_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ r2_yellow_0(X0_51,X3_52)
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(X3_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k2_yellow_0(X0_51,X3_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_76645,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X1_52,X2_52)
    | r1_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(X1_52))
    | ~ r2_yellow_0(X0_51,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k2_yellow_0(X0_51,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_98061,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_76645])).

cnf(c_98063,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_98061])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X0,X3)
    | r1_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_354,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X0_52,X2_52)
    | r1_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_69149,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,X1_52,sK2(sK6,X0_52,sK7))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,X1_52,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_73661,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_69149])).

cnf(c_73663,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_73661])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_352,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X1_52,X2_52)
    | r1_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_69831,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,X2_52,sK7))
    | r1_lattice3(sK6,X0_52,sK2(sK6,X2_52,sK7))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X2_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_71134,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_69831])).

cnf(c_71136,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_71134])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_351,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X1_52,X2_52)
    | r1_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_69830,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,X2_52,sK7))
    | r1_lattice3(sK6,X0_52,sK2(sK6,X2_52,sK7))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,X1_52,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X2_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_71053,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_69830])).

cnf(c_71055,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_71053])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_355,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X0_52,X2_52)
    | r1_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_69150,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,X1_52,sK2(sK6,X0_52,sK7))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_70961,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_69150])).

cnf(c_70963,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_70961])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_341,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_41837,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_366,plain,
    ( r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52))
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52))
    | ~ r2_yellow_0(X0_51,X1_52)
    | r2_yellow_0(X0_51,X0_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_41811,plain,
    ( r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_41825,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,X2_52) != iProver_top
    | r1_lattice3(X0_51,X0_52,X2_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_43789,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK2(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41825])).

cnf(c_2,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_365,plain,
    ( m1_subset_1(sK2(X0_51,X0_52,X1_52),u1_struct_0(X0_51))
    | ~ r2_yellow_0(X0_51,X0_52)
    | r2_yellow_0(X0_51,X1_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_41812,plain,
    ( m1_subset_1(sK2(X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_46419,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43789,c_41812])).

cnf(c_46435,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_46419])).

cnf(c_46437,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_46435])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ r1_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r2_yellow_0(X0,X2)
    | r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_367,plain,
    ( ~ r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52))
    | ~ r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52))
    | ~ r2_yellow_0(X0_51,X1_52)
    | r2_yellow_0(X0_51,X0_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_387,plain,
    ( r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) != iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_41822,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,X2_52) != iProver_top
    | r1_lattice3(X0_51,X1_52,X2_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_43715,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK2(X0_51,X2_52,X0_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41822])).

cnf(c_44267,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43715,c_41812])).

cnf(c_44279,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_44267])).

cnf(c_44281,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_44279])).

cnf(c_47630,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46437,c_387,c_44281])).

cnf(c_41823,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,X2_52) != iProver_top
    | r1_lattice3(X0_51,X1_52,X2_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_43977,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X2_52,X0_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41823])).

cnf(c_47105,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X2_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43977,c_41812])).

cnf(c_47123,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_47105])).

cnf(c_47125,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_47123])).

cnf(c_41826,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,X2_52) != iProver_top
    | r1_lattice3(X0_51,X0_52,X2_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_47796,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP1(X2_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_47125,c_41826])).

cnf(c_68590,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP1(X2_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_47796,c_41812])).

cnf(c_44051,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41826])).

cnf(c_49957,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44051,c_41812])).

cnf(c_49979,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_49957])).

cnf(c_49981,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_49979])).

cnf(c_68592,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68590,c_387,c_47125,c_49981])).

cnf(c_68593,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_68592])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k2_yellow_0(sK6,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_347,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | k2_yellow_0(sK6,sK9(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_41828,plain,
    ( k2_yellow_0(sK6,sK9(X0_52)) = X0_52
    | r2_hidden(X0_52,sK8) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_68597,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,X1_52) = iProver_top
    | v3_orders_2(sK6) != iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_68593,c_41828])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( v3_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( v4_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_69197,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,X1_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68597,c_31,c_32,c_33,c_34])).

cnf(c_69198,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,X1_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_69197])).

cnf(c_69212,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | sP1(sK8,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,sK8) = iProver_top
    | v3_orders_2(sK6) != iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_47630,c_69198])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_69625,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | sP1(sK8,sK6,X0_52) = iProver_top
    | k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69212,c_31,c_32,c_33,c_34,c_36])).

cnf(c_69626,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | sP1(sK8,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) != iProver_top
    | r2_yellow_0(sK6,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_69625])).

cnf(c_69636,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8)
    | sP1(sK8,sK6,sK7) = iProver_top
    | sP0(sK6,sK7) = iProver_top
    | r2_yellow_0(sK6,sK7) != iProver_top
    | r2_yellow_0(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_41837,c_69626])).

cnf(c_18,negated_conjecture,
    ( r2_yellow_0(sK6,sK7)
    | r2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_55,plain,
    ( r2_yellow_0(sK6,sK7) = iProver_top
    | r2_yellow_0(sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_358,plain,
    ( ~ sP0(X0_51,X0_52)
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_21477,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | r2_yellow_0(sK6,X0)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_343,negated_conjecture,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | r2_yellow_0(sK6,X0_52)
    | ~ v1_finset_1(X0_52)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_21484,plain,
    ( k1_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_22615,plain,
    ( sK4(X0_51,sK7) = k1_xboole_0
    | sP0(X0_51,sK7) != iProver_top
    | r2_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top
    | v1_finset_1(sK4(X0_51,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21477,c_21484])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1)
    | v1_finset_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_357,plain,
    ( ~ sP0(X0_51,X0_52)
    | v1_finset_1(sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_21478,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | v1_finset_1(sK4(X0_51,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1)
    | sK4(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_359,plain,
    ( ~ sP0(X0_51,X0_52)
    | sK4(X0_51,X0_52) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_21476,plain,
    ( sK4(X0_51,X0_52) != k1_xboole_0
    | sP0(X0_51,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_22814,plain,
    ( sP0(X0_51,sK7) != iProver_top
    | r2_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22615,c_21478,c_21476])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_yellow_0(X0,sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_360,plain,
    ( ~ sP0(X0_51,X0_52)
    | ~ r2_yellow_0(X0_51,sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_21475,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,sK4(X0_51,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_22818,plain,
    ( sP0(sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_22814,c_21475])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_362,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_21473,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK6,X0),sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_348,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK6,X0_52),sK8)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0_52)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_21479,plain,
    ( k1_xboole_0 = X0_52
    | r2_hidden(k2_yellow_0(sK6,X0_52),sK8) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ r2_hidden(k2_yellow_0(X1,sK3(X0,X1,X2)),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_364,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | ~ r2_hidden(k2_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_21471,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | r2_hidden(k2_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_22730,plain,
    ( sK3(sK8,sK6,X0_52) = k1_xboole_0
    | sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(sK3(sK8,sK6,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21479,c_21471])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2)
    | v1_finset_1(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_361,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_21474,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2)
    | sK3(X0,X1,X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_363,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | sK3(X0_52,X0_51,X1_52) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_21472,plain,
    ( sK3(X0_52,X0_51,X1_52) != k1_xboole_0
    | sP1(X0_52,X0_51,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_22825,plain,
    ( sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22730,c_21474,c_21472])).

cnf(c_22829,plain,
    ( sP1(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_21473,c_22825])).

cnf(c_43788,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK2(X0_51,X2_52,X1_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41825])).

cnf(c_46027,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43788,c_41812])).

cnf(c_46043,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_46027])).

cnf(c_46045,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_46043])).

cnf(c_43716,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK2(X0_51,X0_52,X2_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41822])).

cnf(c_44863,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43716,c_41812])).

cnf(c_44875,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_44863])).

cnf(c_44877,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_44875])).

cnf(c_41810,plain,
    ( r1_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52)) != iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52)) != iProver_top
    | r2_yellow_0(X0_51,X1_52) != iProver_top
    | r2_yellow_0(X0_51,X0_52) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_45247,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) != iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_44877,c_41810])).

cnf(c_47614,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46045,c_45247])).

cnf(c_43978,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X0_52,X2_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41823])).

cnf(c_47965,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X2_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X2_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43978,c_41812])).

cnf(c_47983,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_47965])).

cnf(c_47985,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X1_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_47983])).

cnf(c_48490,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP1(X2_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X2_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X2_52,X1_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_47985,c_41825])).

cnf(c_63141,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP1(X2_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | r2_hidden(sK5(X0_51,X1_52,X2_52),X2_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_48490,c_41812])).

cnf(c_48493,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) != iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_47985,c_41810])).

cnf(c_44050,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(sK2(X0_51,X2_52,X1_52),u1_struct_0(X0_51)) != iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_41811,c_41826])).

cnf(c_49548,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X2_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X2_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X2_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44050,c_41812])).

cnf(c_49570,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_49548])).

cnf(c_49572,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | r1_lattice3(X0_51,X0_52,sK2(X0_51,X0_52,X1_52)) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_49570])).

cnf(c_63143,plain,
    ( m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63141,c_48493,c_49572])).

cnf(c_63144,plain,
    ( sP1(X0_52,X0_51,X1_52) = iProver_top
    | sP0(X0_51,X1_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK5(X0_51,X1_52,X0_52),u1_struct_0(X0_51)) = iProver_top
    | r2_yellow_0(X0_51,X0_52) != iProver_top
    | r2_yellow_0(X0_51,X1_52) = iProver_top
    | v3_orders_2(X0_51) != iProver_top
    | v4_orders_2(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_orders_2(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_63143])).

cnf(c_63148,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X1_52) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | v3_orders_2(sK6) != iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_63144,c_41828])).

cnf(c_63502,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X1_52) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63148,c_31,c_32,c_33,c_34])).

cnf(c_63503,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,X1_52))) = sK5(sK6,X0_52,X1_52)
    | sP1(X1_52,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | r2_hidden(sK5(sK6,X0_52,X1_52),sK8) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X1_52) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_63502])).

cnf(c_63517,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | sP1(sK8,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top
    | v3_orders_2(sK6) != iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_47614,c_63503])).

cnf(c_66214,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | sP1(sK8,sK6,X0_52) = iProver_top
    | k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63517,c_31,c_32,c_33,c_34,c_36])).

cnf(c_66215,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,X0_52,sK8))) = sK5(sK6,X0_52,sK8)
    | sP1(sK8,sK6,X0_52) = iProver_top
    | sP0(sK6,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_yellow_0(sK6,X0_52) = iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_66214])).

cnf(c_66225,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8)
    | sP1(sK8,sK6,sK7) = iProver_top
    | sP0(sK6,sK7) = iProver_top
    | r2_yellow_0(sK6,sK7) = iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_41837,c_66215])).

cnf(c_17,negated_conjecture,
    ( ~ r2_yellow_0(sK6,sK7)
    | ~ r2_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_56,plain,
    ( r2_yellow_0(sK6,sK7) != iProver_top
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_66270,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8)
    | r2_yellow_0(sK6,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66225,c_56,c_22818,c_22829])).

cnf(c_69681,plain,
    ( k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_69636,c_55,c_22818,c_22829,c_66270])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_356,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X0_52,X2_52)
    | r1_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ r2_yellow_0(X0_51,X3_52)
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(X3_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k2_yellow_0(X0_51,X3_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_42911,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X0_52,X2_52)
    | r1_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X3_52)),k1_zfmisc_1(X1_52))
    | ~ r2_yellow_0(X0_51,sK9(sK5(sK6,sK7,X3_52)))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X3_52)))
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k2_yellow_0(X0_51,sK9(sK5(sK6,sK7,X3_52))) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_45445,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,X1_52)
    | r1_lattice3(sK6,sK7,X1_52)
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_42911])).

cnf(c_65182,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_45445])).

cnf(c_65184,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_65182])).

cnf(c_65172,plain,
    ( ~ r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | ~ r2_yellow_0(sK6,X0_52)
    | r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_65174,plain,
    ( ~ r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | r2_yellow_0(sK6,sK7)
    | ~ r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_65172])).

cnf(c_63069,plain,
    ( r1_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r1_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | ~ r2_yellow_0(sK6,X0_52)
    | r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_63071,plain,
    ( r1_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | r2_yellow_0(sK6,sK7)
    | ~ r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_63069])).

cnf(c_63064,plain,
    ( m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,X0_52)
    | r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_63066,plain,
    ( m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK7)
    | ~ r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_63064])).

cnf(c_42469,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X2_52))
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X2_52))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X2_52),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_57353,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42469])).

cnf(c_57355,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_57353])).

cnf(c_42468,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X2_52))
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X2_52))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,X1_52,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,X2_52),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_57333,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42468])).

cnf(c_57335,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_57333])).

cnf(c_55760,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_45445])).

cnf(c_55762,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_55760])).

cnf(c_42912,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r1_lattice3(X0_51,X1_52,X2_52)
    | r1_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X3_52)),k1_zfmisc_1(X1_52))
    | ~ r2_yellow_0(X0_51,sK9(sK5(sK6,sK7,X3_52)))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X3_52)))
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k2_yellow_0(X0_51,sK9(sK5(sK6,sK7,X3_52))) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_45444,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,X1_52)
    | ~ r1_lattice3(sK6,sK7,X1_52)
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_42912])).

cnf(c_55557,plain,
    ( sP1(X0_52,sK6,sK7)
    | r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_45444])).

cnf(c_55559,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_55557])).

cnf(c_370,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_43952,plain,
    ( X0_52 != X1_52
    | X0_52 = k2_yellow_0(sK6,X2_52)
    | k2_yellow_0(sK6,X2_52) != X1_52 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_43963,plain,
    ( X0_52 != sK5(sK6,sK7,X1_52)
    | X0_52 = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X1_52)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X1_52))) != sK5(sK6,sK7,X1_52) ),
    inference(instantiation,[status(thm)],[c_43952])).

cnf(c_44828,plain,
    ( sK5(sK6,sK7,X0_52) != sK5(sK6,sK7,X0_52)
    | sK5(sK6,sK7,X0_52) = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) != sK5(sK6,sK7,X0_52) ),
    inference(instantiation,[status(thm)],[c_43963])).

cnf(c_44829,plain,
    ( sK5(sK6,sK7,X0_52) = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) != sK5(sK6,sK7,X0_52) ),
    inference(equality_resolution_simp,[status(thm)],[c_44828])).

cnf(c_44830,plain,
    ( sK5(sK6,sK7,sK8) = k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | k2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) != sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_44829])).

cnf(c_43324,plain,
    ( ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | r2_yellow_0(sK6,X0_52)
    | ~ r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_43326,plain,
    ( ~ r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r2_yellow_0(sK6,sK7)
    | r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_43324])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0),k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_345,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0_52),k1_zfmisc_1(sK7)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_42686,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_346,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_42687,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | r2_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_344,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_42688,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | v1_finset_1(sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_42374,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X0_52))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_42667,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42374])).

cnf(c_42669,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42667])).

cnf(c_42373,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,X1_52,sK2(sK6,sK7,X0_52))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,X1_52,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_42624,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42373])).

cnf(c_42626,plain,
    ( sP1(sK8,sK6,sK7)
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | m1_subset_1(sK5(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42624])).

cnf(c_42298,plain,
    ( r1_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r1_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | r2_yellow_0(sK6,X0_52)
    | ~ r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_42300,plain,
    ( r1_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r1_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r2_yellow_0(sK6,sK7)
    | r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42298])).

cnf(c_42291,plain,
    ( m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | r2_yellow_0(sK6,X0_52)
    | ~ r2_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_42293,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ r2_yellow_0(sK6,sK7)
    | r2_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_42291])).

cnf(c_22830,plain,
    ( ~ sP1(sK8,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22829])).

cnf(c_22819,plain,
    ( ~ sP0(sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22818])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98063,c_73663,c_71136,c_71055,c_70963,c_69681,c_65184,c_65174,c_63071,c_63066,c_57355,c_57335,c_55762,c_55559,c_44830,c_43326,c_42686,c_42687,c_42688,c_42669,c_42626,c_42300,c_42293,c_22830,c_22819,c_17,c_18,c_25,c_26,c_27,c_28,c_29,c_30])).


%------------------------------------------------------------------------------
