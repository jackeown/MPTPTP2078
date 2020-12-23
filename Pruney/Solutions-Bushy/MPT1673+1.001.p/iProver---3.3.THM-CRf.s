%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:09 EST 2020

% Result     : Theorem 23.68s
% Output     : CNFRefutation 23.68s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 691 expanded)
%              Number of clauses        :  141 ( 185 expanded)
%              Number of leaves         :   16 ( 179 expanded)
%              Depth                    :   18
%              Number of atoms          : 1503 (10261 expanded)
%              Number of equality atoms :  193 (1328 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   48 (   5 average)
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
    inference(rectify,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r1_yellow_0(X0,X6)
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
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r1_yellow_0(X0,X6)
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
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
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
                  ( ( r2_lattice3(X0,X1,X7)
                  <=> r2_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
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
                  ( ( ( r2_lattice3(X0,X1,X7)
                      | ~ r2_lattice3(X0,X2,X7) )
                    & ( r2_lattice3(X0,X2,X7)
                      | ~ r2_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
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
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k1_yellow_0(X0,X5) != X4
                      | ~ r1_yellow_0(X0,X5)
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
              ( k1_yellow_0(X0,X5) != X4
              | ~ r1_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( k1_yellow_0(X0,X5) != sK5(X0,X1,X2)
            | ~ r1_yellow_0(X0,X5)
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
                  ( ( ( r2_lattice3(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ( ! [X5] :
                    ( k1_yellow_0(X0,X5) != sK5(X0,X1,X2)
                    | ~ r1_yellow_0(X0,X5)
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

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k1_yellow_0(X0,X5) != sK5(X0,X1,X2)
      | ~ r1_yellow_0(X0,X5)
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

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k1_yellow_0(X0,X5) != sK5(X0,X1,X2)
      | ~ r1_yellow_0(X0,X5)
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

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
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

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
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
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
               => ( r1_yellow_0(X0,X1)
                <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
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
                 => ( r1_yellow_0(X0,X1)
                  <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
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
                 => ( r1_yellow_0(X0,X1)
                  <=> r1_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_yellow_0(X0,X1)
              <~> r1_yellow_0(X0,X2) )
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_yellow_0(X0,X1)
              <~> r1_yellow_0(X0,X2) )
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(X0,X2)
                | ~ r1_yellow_0(X0,X1) )
              & ( r1_yellow_0(X0,X2)
                | r1_yellow_0(X0,X1) )
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(X0,X2)
                | ~ r1_yellow_0(X0,X1) )
              & ( r1_yellow_0(X0,X2)
                | r1_yellow_0(X0,X1) )
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( k1_yellow_0(X0,X5) = X4
          & r1_yellow_0(X0,X5)
          & m1_subset_1(X5,k1_zfmisc_1(X1))
          & v1_finset_1(X5) )
     => ( k1_yellow_0(X0,sK9(X4)) = X4
        & r1_yellow_0(X0,sK9(X4))
        & m1_subset_1(sK9(X4),k1_zfmisc_1(X1))
        & v1_finset_1(sK9(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_yellow_0(X0,X2)
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X2)
            | r1_yellow_0(X0,X1) )
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
     => ( ( ~ r1_yellow_0(X0,sK8)
          | ~ r1_yellow_0(X0,X1) )
        & ( r1_yellow_0(X0,sK8)
          | r1_yellow_0(X0,X1) )
        & ! [X3] :
            ( r2_hidden(k1_yellow_0(X0,X3),sK8)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k1_yellow_0(X0,X5) = X4
                & r1_yellow_0(X0,X5)
                & m1_subset_1(X5,k1_zfmisc_1(X1))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,sK8)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & ! [X6] :
            ( r1_yellow_0(X0,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(X0,X2)
                | ~ r1_yellow_0(X0,X1) )
              & ( r1_yellow_0(X0,X2)
                | r1_yellow_0(X0,X1) )
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
     => ( ? [X2] :
            ( ( ~ r1_yellow_0(X0,X2)
              | ~ r1_yellow_0(X0,sK7) )
            & ( r1_yellow_0(X0,X2)
              | r1_yellow_0(X0,sK7) )
            & ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k1_yellow_0(X0,X5) = X4
                    & r1_yellow_0(X0,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(sK7))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & ! [X6] :
                ( r1_yellow_0(X0,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_yellow_0(X0,X2)
                  | ~ r1_yellow_0(X0,X1) )
                & ( r1_yellow_0(X0,X2)
                  | r1_yellow_0(X0,X1) )
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
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_yellow_0(sK6,X2)
                | ~ r1_yellow_0(sK6,X1) )
              & ( r1_yellow_0(sK6,X2)
                | r1_yellow_0(sK6,X1) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(sK6,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(sK6,X5) = X4
                      & r1_yellow_0(sK6,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
              & ! [X6] :
                  ( r1_yellow_0(sK6,X6)
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

fof(f42,plain,
    ( ( ~ r1_yellow_0(sK6,sK8)
      | ~ r1_yellow_0(sK6,sK7) )
    & ( r1_yellow_0(sK6,sK8)
      | r1_yellow_0(sK6,sK7) )
    & ! [X3] :
        ( r2_hidden(k1_yellow_0(sK6,X3),sK8)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k1_yellow_0(sK6,sK9(X4)) = X4
          & r1_yellow_0(sK6,sK9(X4))
          & m1_subset_1(sK9(X4),k1_zfmisc_1(sK7))
          & v1_finset_1(sK9(X4)) )
        | ~ r2_hidden(X4,sK8)
        | ~ m1_subset_1(X4,u1_struct_0(sK6)) )
    & ! [X6] :
        ( r1_yellow_0(sK6,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f37,f41,f40,f39,f38])).

fof(f72,plain,(
    ! [X4] :
      ( k1_yellow_0(sK6,sK9(X4)) = X4
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X4] :
      ( m1_subset_1(sK9(X4),k1_zfmisc_1(sK7))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ! [X4] :
      ( r1_yellow_0(sK6,sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X4] :
      ( v1_finset_1(sK9(X4))
      | ~ r2_hidden(X4,sK8)
      | ~ m1_subset_1(X4,u1_struct_0(sK6)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r1_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r1_yellow_0(X0,sK4(X0,X1))
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,sK4(X0,X1))
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X6] :
      ( r1_yellow_0(sK6,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X6] :
      ( r1_yellow_0(sK6,X6)
      | o_0_0_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X6) ) ),
    inference(definition_unfolding,[],[f68,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != sK4(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k1_yellow_0(X1,sK3(X0,X1,X2)),X0)
        & k1_xboole_0 != sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_yellow_0(X1,sK3(X0,X1,X2)),X0)
        & k1_xboole_0 != sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK6,X3),sK8)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK6,X3),sK8)
      | o_0_0_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK7))
      | ~ v1_finset_1(X3) ) ),
    inference(definition_unfolding,[],[f73,f43])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X1,sK3(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK3(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != sK3(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f75,plain,
    ( ~ r1_yellow_0(sK6,sK8)
    | ~ r1_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( r1_yellow_0(sK6,sK8)
    | r1_yellow_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( sP1(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | r2_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k1_yellow_0(X1,X4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_365,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r2_lattice3(X0_51,X1_52,X2_52)
    | r2_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ r1_yellow_0(X0_51,X3_52)
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(X3_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k1_yellow_0(X0_51,X3_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_66839,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X1_52,sK2(sK6,X2_52,sK7))
    | r2_lattice3(sK6,X0_52,sK2(sK6,X2_52,sK7))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X2_52,sK7),u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,X3_52)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(X3_52)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1_52,X0_52) != k1_yellow_0(sK6,X3_52) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_75313,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,X2_52)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(X2_52)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,X2_52) ),
    inference(instantiation,[status(thm)],[c_66839])).

cnf(c_75331,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X2_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X2_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52))) ),
    inference(instantiation,[status(thm)],[c_75313])).

cnf(c_75333,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_75331])).

cnf(c_12,plain,
    ( sP1(X0,X1,X2)
    | ~ r2_lattice3(X1,X0,X3)
    | r2_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X4)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_finset_1(X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X1,X2,X0) != k1_yellow_0(X1,X4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_368,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r2_lattice3(X0_51,X0_52,X2_52)
    | r2_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ r1_yellow_0(X0_51,X3_52)
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | ~ v1_finset_1(X3_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51)
    | sK5(X0_51,X1_52,X0_52) != k1_yellow_0(X0_51,X3_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_65832,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r2_lattice3(sK6,X1_52,sK2(sK6,X0_52,sK7))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,X2_52)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(X2_52)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1_52,X0_52) != k1_yellow_0(sK6,X2_52) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_69446,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r2_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_65832])).

cnf(c_69449,plain,
    ( sP1(sK8,sK6,sK7)
    | r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_69446])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | r2_lattice3(X1,X0,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_364,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r2_lattice3(X0_51,X1_52,X2_52)
    | r2_lattice3(X0_51,X0_52,X2_52)
    | sP0(X0_51,X1_52)
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_66840,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X1_52,sK2(sK6,X2_52,sK7))
    | r2_lattice3(sK6,X0_52,sK2(sK6,X2_52,sK7))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X2_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_68536,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,X1_52,sK7))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,X1_52,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X1_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_66840])).

cnf(c_68538,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_68536])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ r2_lattice3(X1,X0,X3)
    | r2_lattice3(X1,X2,X3)
    | sP0(X1,X2)
    | r2_hidden(sK5(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_367,plain,
    ( sP1(X0_52,X0_51,X1_52)
    | ~ r2_lattice3(X0_51,X0_52,X2_52)
    | r2_lattice3(X0_51,X1_52,X2_52)
    | sP0(X0_51,X1_52)
    | r2_hidden(sK5(X0_51,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_52,u1_struct_0(X0_51))
    | ~ v3_orders_2(X0_51)
    | ~ v4_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_65834,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r2_lattice3(sK6,X1_52,sK2(sK6,X0_52,sK7))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_66898,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r2_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_65834])).

cnf(c_66900,plain,
    ( sP1(sK8,sK6,sK7)
    | r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_66898])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,X1,sK2(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_380,plain,
    ( ~ r2_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52))
    | ~ r2_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52))
    | ~ r1_yellow_0(X0_51,X1_52)
    | r1_yellow_0(X0_51,X0_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_65841,plain,
    ( ~ r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | ~ r1_yellow_0(sK6,X0_52)
    | r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_65843,plain,
    ( ~ r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | r1_yellow_0(sK6,sK7)
    | ~ r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_65841])).

cnf(c_1,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X2,X1))
    | r2_lattice3(X0,X2,sK2(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_379,plain,
    ( r2_lattice3(X0_51,X0_52,sK2(X0_51,X1_52,X0_52))
    | r2_lattice3(X0_51,X1_52,sK2(X0_51,X1_52,X0_52))
    | ~ r1_yellow_0(X0_51,X1_52)
    | r1_yellow_0(X0_51,X0_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_65648,plain,
    ( r2_lattice3(sK6,X0_52,sK2(sK6,X0_52,sK7))
    | r2_lattice3(sK6,sK7,sK2(sK6,X0_52,sK7))
    | ~ r1_yellow_0(sK6,X0_52)
    | r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_65650,plain,
    ( r2_lattice3(sK6,sK7,sK2(sK6,sK8,sK7))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK8,sK7))
    | r1_yellow_0(sK6,sK7)
    | ~ r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_65648])).

cnf(c_2,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_378,plain,
    ( m1_subset_1(sK2(X0_51,X0_52,X1_52),u1_struct_0(X0_51))
    | ~ r1_yellow_0(X0_51,X0_52)
    | r1_yellow_0(X0_51,X1_52)
    | v2_struct_0(X0_51)
    | ~ l1_orders_2(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_65643,plain,
    ( m1_subset_1(sK2(sK6,X0_52,sK7),u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,X0_52)
    | r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_65645,plain,
    ( m1_subset_1(sK2(sK6,sK8,sK7),u1_struct_0(sK6))
    | r1_yellow_0(sK6,sK7)
    | ~ r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_65643])).

cnf(c_62220,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,X1_52,sK2(sK6,sK7,X0_52))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(X1_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,X2_52)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(X2_52)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1_52,X0_52) != k1_yellow_0(sK6,X2_52) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_63256,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,X1_52,sK2(sK6,sK7,X0_52))
    | sP0(sK6,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X2_52)),k1_zfmisc_1(X1_52))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X2_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,X1_52,X0_52) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52))) ),
    inference(instantiation,[status(thm)],[c_62220])).

cnf(c_65446,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X0_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_63256])).

cnf(c_65448,plain,
    ( sP1(sK8,sK6,sK7)
    | r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_65446])).

cnf(c_383,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_63412,plain,
    ( X0_52 != X1_52
    | sK5(sK6,sK7,X2_52) != X1_52
    | sK5(sK6,sK7,X2_52) = X0_52 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_65240,plain,
    ( X0_52 != sK5(sK6,sK7,X1_52)
    | sK5(sK6,sK7,X1_52) = X0_52
    | sK5(sK6,sK7,X1_52) != sK5(sK6,sK7,X1_52) ),
    inference(instantiation,[status(thm)],[c_63412])).

cnf(c_65241,plain,
    ( X0_52 != sK5(sK6,sK7,X1_52)
    | sK5(sK6,sK7,X1_52) = X0_52 ),
    inference(equality_resolution_simp,[status(thm)],[c_65240])).

cnf(c_65282,plain,
    ( sK5(sK6,sK7,X0_52) = k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52)))
    | k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) != sK5(sK6,sK7,X0_52) ),
    inference(instantiation,[status(thm)],[c_65241])).

cnf(c_65283,plain,
    ( sK5(sK6,sK7,sK8) = k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) != sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_65282])).

cnf(c_62122,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,X2_52)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(X2_52)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,X2_52) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_63294,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,X2_52)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,X2_52)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,X0_52) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X2_52))) ),
    inference(instantiation,[status(thm)],[c_62122])).

cnf(c_63296,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v1_finset_1(sK9(sK5(sK6,sK7,sK8)))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6)
    | sK5(sK6,sK7,sK8) != k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_63294])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_yellow_0(sK6,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_359,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | k1_yellow_0(sK6,sK9(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_354,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_56184,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | m1_subset_1(X0_52,X2_52)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X2_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_56164,plain,
    ( r2_hidden(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,X2_52) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(X2_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_57481,plain,
    ( r2_hidden(X0_52,sK8) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_56184,c_56164])).

cnf(c_56174,plain,
    ( k1_yellow_0(sK6,sK9(X0_52)) = X0_52
    | r2_hidden(X0_52,sK8) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_57540,plain,
    ( k1_yellow_0(sK6,sK9(X0_52)) = X0_52
    | r2_hidden(X0_52,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_57481,c_56174])).

cnf(c_57557,plain,
    ( ~ r2_hidden(X0_52,sK8)
    | k1_yellow_0(sK6,sK9(X0_52)) = X0_52 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57540])).

cnf(c_61337,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | k1_yellow_0(sK6,sK9(X0_52)) = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_57557])).

cnf(c_62752,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,X0_52),sK8)
    | k1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) = sK5(sK6,sK7,X0_52) ),
    inference(instantiation,[status(thm)],[c_61337])).

cnf(c_62769,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | k1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) = sK5(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_62752])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0),k1_zfmisc_1(sK7)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_357,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | m1_subset_1(sK9(X0_52),k1_zfmisc_1(sK7)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_57521,plain,
    ( ~ r2_hidden(X0_52,sK8)
    | m1_subset_1(X0_52,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57481])).

cnf(c_60884,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | m1_subset_1(sK9(X0_52),k1_zfmisc_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_57521])).

cnf(c_61328,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | m1_subset_1(sK9(X0_52),k1_zfmisc_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_60884])).

cnf(c_62753,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,X0_52),sK8)
    | m1_subset_1(sK9(sK5(sK6,sK7,X0_52)),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_61328])).

cnf(c_62765,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | m1_subset_1(sK9(sK5(sK6,sK7,sK8)),k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_62753])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_yellow_0(sK6,sK9(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_358,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | r1_yellow_0(sK6,sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_56175,plain,
    ( r2_hidden(X0_52,sK8) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK6)) != iProver_top
    | r1_yellow_0(sK6,sK9(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_57539,plain,
    ( r2_hidden(X0_52,sK8) != iProver_top
    | r1_yellow_0(sK6,sK9(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_57481,c_56175])).

cnf(c_57554,plain,
    ( ~ r2_hidden(X0_52,sK8)
    | r1_yellow_0(sK6,sK9(X0_52)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57539])).

cnf(c_61317,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | r1_yellow_0(sK6,sK9(X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_57554])).

cnf(c_62754,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,X0_52),sK8)
    | r1_yellow_0(sK6,sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_61317])).

cnf(c_62761,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | r1_yellow_0(sK6,sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_62754])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_356,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK6))
    | v1_finset_1(sK9(X0_52)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_56177,plain,
    ( r2_hidden(X0_52,sK8) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK6)) != iProver_top
    | v1_finset_1(sK9(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_57541,plain,
    ( r2_hidden(X0_52,sK8) != iProver_top
    | v1_finset_1(sK9(X0_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_57481,c_56177])).

cnf(c_57560,plain,
    ( ~ r2_hidden(X0_52,sK8)
    | v1_finset_1(sK9(X0_52)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57541])).

cnf(c_61308,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK8)
    | v1_finset_1(sK9(X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_57560])).

cnf(c_62755,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,X0_52),sK8)
    | v1_finset_1(sK9(sK5(sK6,sK7,X0_52))) ),
    inference(instantiation,[status(thm)],[c_61308])).

cnf(c_62757,plain,
    ( ~ r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | v1_finset_1(sK9(sK5(sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_62755])).

cnf(c_62222,plain,
    ( sP1(X0_52,sK6,X1_52)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,X1_52,sK2(sK6,sK7,X0_52))
    | sP0(sK6,X1_52)
    | r2_hidden(sK5(sK6,X1_52,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_62459,plain,
    ( sP1(X0_52,sK6,sK7)
    | ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_62222])).

cnf(c_62461,plain,
    ( sP1(sK8,sK6,sK7)
    | r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_62459])).

cnf(c_62152,plain,
    ( ~ r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | r1_yellow_0(sK6,X0_52)
    | ~ r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_62154,plain,
    ( ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | ~ r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r1_yellow_0(sK6,sK7)
    | r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_62152])).

cnf(c_62123,plain,
    ( sP1(X0_52,sK6,sK7)
    | r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X1_52))
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,X1_52))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7,X1_52),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_62130,plain,
    ( sP1(sK8,sK6,sK7)
    | ~ r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | sP0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7,sK8),sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_62123])).

cnf(c_61962,plain,
    ( r2_lattice3(sK6,X0_52,sK2(sK6,sK7,X0_52))
    | r2_lattice3(sK6,sK7,sK2(sK6,sK7,X0_52))
    | r1_yellow_0(sK6,X0_52)
    | ~ r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_61964,plain,
    ( r2_lattice3(sK6,sK7,sK2(sK6,sK7,sK8))
    | r2_lattice3(sK6,sK8,sK2(sK6,sK7,sK8))
    | ~ r1_yellow_0(sK6,sK7)
    | r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_61962])).

cnf(c_61933,plain,
    ( m1_subset_1(sK2(sK6,sK7,X0_52),u1_struct_0(sK6))
    | r1_yellow_0(sK6,X0_52)
    | ~ r1_yellow_0(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_61935,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,sK7)
    | r1_yellow_0(sK6,sK8)
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_61933])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_370,plain,
    ( ~ sP0(X0_51,X0_52)
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_56171,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | m1_subset_1(sK4(X0_51,X0_52),k1_zfmisc_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | r1_yellow_0(sK6,X0)
    | ~ v1_finset_1(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_355,negated_conjecture,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | r1_yellow_0(sK6,X0_52)
    | ~ v1_finset_1(X0_52)
    | o_0_0_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_56178,plain,
    ( o_0_0_xboole_0 = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | r1_yellow_0(sK6,X0_52) = iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_57290,plain,
    ( sK4(X0_51,sK7) = o_0_0_xboole_0
    | sP0(X0_51,sK7) != iProver_top
    | r1_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top
    | v1_finset_1(sK4(X0_51,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56171,c_56178])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1)
    | v1_finset_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_369,plain,
    ( ~ sP0(X0_51,X0_52)
    | v1_finset_1(sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_56172,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | v1_finset_1(sK4(X0_51,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1)
    | sK4(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_371,plain,
    ( ~ sP0(X0_51,X0_52)
    | sK4(X0_51,X0_52) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_56170,plain,
    ( sK4(X0_51,X0_52) != o_0_0_xboole_0
    | sP0(X0_51,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_57945,plain,
    ( sP0(X0_51,sK7) != iProver_top
    | r1_yellow_0(sK6,sK4(X0_51,sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57290,c_56172,c_56170])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1)
    | ~ r1_yellow_0(X0,sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_372,plain,
    ( ~ sP0(X0_51,X0_52)
    | ~ r1_yellow_0(X0_51,sK4(X0_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_56169,plain,
    ( sP0(X0_51,X0_52) != iProver_top
    | r1_yellow_0(X0_51,sK4(X0_51,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_57949,plain,
    ( sP0(sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_57945,c_56169])).

cnf(c_57950,plain,
    ( ~ sP0(sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57949])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_374,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_56167,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | m1_subset_1(sK3(X0_52,X0_51,X1_52),k1_zfmisc_1(X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK6,X0),sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_360,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK6,X0_52),sK8)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(sK7))
    | ~ v1_finset_1(X0_52)
    | o_0_0_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_56173,plain,
    ( o_0_0_xboole_0 = X0_52
    | r2_hidden(k1_yellow_0(sK6,X0_52),sK8) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ r2_hidden(k1_yellow_0(X1,sK3(X0,X1,X2)),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_376,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | ~ r2_hidden(k1_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_56165,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | r2_hidden(k1_yellow_0(X0_51,sK3(X0_52,X0_51,X1_52)),X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_57383,plain,
    ( sK3(sK8,sK6,X0_52) = o_0_0_xboole_0
    | sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top
    | v1_finset_1(sK3(sK8,sK6,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56173,c_56165])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2)
    | v1_finset_1(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_373,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_56168,plain,
    ( sP1(X0_52,X0_51,X1_52) != iProver_top
    | v1_finset_1(sK3(X0_52,X0_51,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | sK3(X0,X1,X2) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_375,plain,
    ( ~ sP1(X0_52,X0_51,X1_52)
    | sK3(X0_52,X0_51,X1_52) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_56166,plain,
    ( sK3(X0_52,X0_51,X1_52) != o_0_0_xboole_0
    | sP1(X0_52,X0_51,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_57820,plain,
    ( sP1(sK8,sK6,X0_52) != iProver_top
    | m1_subset_1(sK3(sK8,sK6,X0_52),k1_zfmisc_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57383,c_56168,c_56166])).

cnf(c_57824,plain,
    ( sP1(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_56167,c_57820])).

cnf(c_57825,plain,
    ( ~ sP1(sK8,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_57824])).

cnf(c_18,negated_conjecture,
    ( ~ r1_yellow_0(sK6,sK7)
    | ~ r1_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,negated_conjecture,
    ( r1_yellow_0(sK6,sK7)
    | r1_yellow_0(sK6,sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75333,c_69449,c_68538,c_66900,c_65843,c_65650,c_65645,c_65448,c_65283,c_63296,c_62769,c_62765,c_62761,c_62757,c_62461,c_62154,c_62130,c_61964,c_61935,c_57950,c_57825,c_18,c_19,c_26,c_27,c_28,c_29,c_30,c_31])).


%------------------------------------------------------------------------------
