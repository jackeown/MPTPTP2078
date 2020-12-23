%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:48 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  201 (3211 expanded)
%              Number of clauses        :  128 ( 576 expanded)
%              Number of leaves         :   18 (1057 expanded)
%              Depth                    :   27
%              Number of atoms          :  999 (31130 expanded)
%              Number of equality atoms :  219 ( 650 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_orders_2(X2,X0,X3)
            | ~ r2_xboole_0(X2,X3) )
          & ( m1_orders_2(X2,X0,X3)
            | r2_xboole_0(X2,X3) )
          & m2_orders_2(X3,X0,X1) )
     => ( ( ~ m1_orders_2(X2,X0,sK4)
          | ~ r2_xboole_0(X2,sK4) )
        & ( m1_orders_2(X2,X0,sK4)
          | r2_xboole_0(X2,sK4) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,X0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,X0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,X0,X1) )
          & m2_orders_2(X2,X0,X1) )
     => ( ? [X3] :
            ( ( ~ m1_orders_2(sK3,X0,X3)
              | ~ r2_xboole_0(sK3,X3) )
            & ( m1_orders_2(sK3,X0,X3)
              | r2_xboole_0(sK3,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,X0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,X0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,X0,sK2) )
            & m2_orders_2(X2,X0,sK2) )
        & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK1,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK1,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK1,X1) )
              & m2_orders_2(X2,sK1,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ m1_orders_2(sK3,sK1,sK4)
      | ~ r2_xboole_0(sK3,sK4) )
    & ( m1_orders_2(sK3,sK1,sK4)
      | r2_xboole_0(sK3,sK4) )
    & m2_orders_2(sK4,sK1,sK2)
    & m2_orders_2(sK3,sK1,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f61,f65,f64,f63,f62])).

fof(f104,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f103,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f99,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f109,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f107,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X3,X0,X2)
      | ~ m1_orders_2(X2,X0,X3)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2407,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2408,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4548,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2407,c_2408])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2402,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2400,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3958,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_2400])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2410,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6503,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3958,c_2410])).

cnf(c_7574,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4548,c_6503])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_36,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_688,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_36])).

cnf(c_689,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_772,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 != X3
    | X0 != X4
    | k4_xboole_0(X3,X4) != X3
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_689])).

cnf(c_773,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k4_xboole_0(X0,X2) != X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1038,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k4_xboole_0(X0,X2) != X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_773,c_37])).

cnf(c_1039,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k4_xboole_0(X1,X0) != X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1038])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_39,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1043,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | k4_xboole_0(X1,X0) != X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1039,c_41,c_40,c_39,c_38])).

cnf(c_1282,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | k4_xboole_0(X1,X0) != X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1043])).

cnf(c_2381,plain,
    ( k4_xboole_0(X0,X1) != X0
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_9973,plain,
    ( k1_xboole_0 != X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7574,c_2381])).

cnf(c_9987,plain,
    ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9973])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_33,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_313,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_314,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_590,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_314])).

cnf(c_591,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_2388,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_35,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2391,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2392,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_649,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_650,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1083,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_650,c_37])).

cnf(c_1084,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1083])).

cnf(c_1088,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_41,c_40,c_39,c_38])).

cnf(c_1274,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1088])).

cnf(c_2383,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_3784,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_2383])).

cnf(c_4127,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_3784])).

cnf(c_49,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_311,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_312,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_567,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_312])).

cnf(c_568,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_569,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_26,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_721,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_722,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_1062,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_722,c_37])).

cnf(c_1063,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1062])).

cnf(c_1067,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1063,c_41,c_40,c_39,c_38])).

cnf(c_1278,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1067])).

cnf(c_2632,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_2633,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2632])).

cnf(c_27,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1167,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_1168,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_1167])).

cnf(c_1170,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1168,c_41,c_40,c_39,c_38])).

cnf(c_2648,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2649,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_4136,plain,
    ( m1_orders_2(sK4,sK1,sK3) = iProver_top
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4127,c_49,c_569,c_2633,c_2649])).

cnf(c_4137,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4136])).

cnf(c_31,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_2(X3,X1,X0)
    | ~ m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_610,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_2(X3,X1,X0)
    | ~ m1_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_611,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_1113,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_37])).

cnf(c_1114,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1113])).

cnf(c_1118,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_41,c_40,c_39,c_38])).

cnf(c_1270,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1118])).

cnf(c_2384,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_123,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1172,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_2382,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_25,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1184,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_1185,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_1187,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_41,c_40,c_39,c_38])).

cnf(c_2385,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_2713,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2385])).

cnf(c_2386,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_2714,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2386])).

cnf(c_4516,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | X0 = X1
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2384,c_123,c_1172,c_2713,c_2714])).

cnf(c_4517,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4516])).

cnf(c_4525,plain,
    ( sK3 = X0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_4517])).

cnf(c_4909,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_4525])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_580,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_314])).

cnf(c_581,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_582,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_592,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_3088,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4081,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_3088])).

cnf(c_4082,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4081])).

cnf(c_2755,plain,
    ( m1_orders_2(X0,sK1,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_2714])).

cnf(c_4144,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_2755])).

cnf(c_4912,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4909,c_582,c_592,c_4082,c_4144])).

cnf(c_5126,plain,
    ( sK3 != sK3
    | m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2388,c_4912])).

cnf(c_5127,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5126])).

cnf(c_28,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_25])).

cnf(c_229,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_1143,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_37])).

cnf(c_1144,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1143])).

cnf(c_1148,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1144,c_41,c_40,c_39,c_38])).

cnf(c_2387,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_2712,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_2387])).

cnf(c_5495,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_2712])).

cnf(c_5503,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5127,c_5495])).

cnf(c_5552,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5503,c_5127])).

cnf(c_5565,plain,
    ( m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5552,c_2391])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9987,c_5565])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n005.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 18:08:32 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 2.88/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/0.93  
% 2.88/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.93  
% 2.88/0.93  ------  iProver source info
% 2.88/0.93  
% 2.88/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.93  git: non_committed_changes: false
% 2.88/0.93  git: last_make_outside_of_git: false
% 2.88/0.93  
% 2.88/0.93  ------ 
% 2.88/0.93  
% 2.88/0.93  ------ Input Options
% 2.88/0.93  
% 2.88/0.93  --out_options                           all
% 2.88/0.93  --tptp_safe_out                         true
% 2.88/0.93  --problem_path                          ""
% 2.88/0.93  --include_path                          ""
% 2.88/0.93  --clausifier                            res/vclausify_rel
% 2.88/0.93  --clausifier_options                    --mode clausify
% 2.88/0.93  --stdin                                 false
% 2.88/0.93  --stats_out                             all
% 2.88/0.93  
% 2.88/0.93  ------ General Options
% 2.88/0.93  
% 2.88/0.93  --fof                                   false
% 2.88/0.93  --time_out_real                         305.
% 2.88/0.93  --time_out_virtual                      -1.
% 2.88/0.93  --symbol_type_check                     false
% 2.88/0.93  --clausify_out                          false
% 2.88/0.93  --sig_cnt_out                           false
% 2.88/0.93  --trig_cnt_out                          false
% 2.88/0.93  --trig_cnt_out_tolerance                1.
% 2.88/0.93  --trig_cnt_out_sk_spl                   false
% 2.88/0.93  --abstr_cl_out                          false
% 2.88/0.93  
% 2.88/0.93  ------ Global Options
% 2.88/0.93  
% 2.88/0.93  --schedule                              default
% 2.88/0.93  --add_important_lit                     false
% 2.88/0.93  --prop_solver_per_cl                    1000
% 2.88/0.93  --min_unsat_core                        false
% 2.88/0.93  --soft_assumptions                      false
% 2.88/0.93  --soft_lemma_size                       3
% 2.88/0.93  --prop_impl_unit_size                   0
% 2.88/0.93  --prop_impl_unit                        []
% 2.88/0.93  --share_sel_clauses                     true
% 2.88/0.93  --reset_solvers                         false
% 2.88/0.93  --bc_imp_inh                            [conj_cone]
% 2.88/0.93  --conj_cone_tolerance                   3.
% 2.88/0.93  --extra_neg_conj                        none
% 2.88/0.93  --large_theory_mode                     true
% 2.88/0.93  --prolific_symb_bound                   200
% 2.88/0.93  --lt_threshold                          2000
% 2.88/0.93  --clause_weak_htbl                      true
% 2.88/0.93  --gc_record_bc_elim                     false
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing Options
% 2.88/0.93  
% 2.88/0.93  --preprocessing_flag                    true
% 2.88/0.93  --time_out_prep_mult                    0.1
% 2.88/0.93  --splitting_mode                        input
% 2.88/0.93  --splitting_grd                         true
% 2.88/0.93  --splitting_cvd                         false
% 2.88/0.93  --splitting_cvd_svl                     false
% 2.88/0.93  --splitting_nvd                         32
% 2.88/0.93  --sub_typing                            true
% 2.88/0.93  --prep_gs_sim                           true
% 2.88/0.93  --prep_unflatten                        true
% 2.88/0.93  --prep_res_sim                          true
% 2.88/0.93  --prep_upred                            true
% 2.88/0.93  --prep_sem_filter                       exhaustive
% 2.88/0.93  --prep_sem_filter_out                   false
% 2.88/0.93  --pred_elim                             true
% 2.88/0.93  --res_sim_input                         true
% 2.88/0.93  --eq_ax_congr_red                       true
% 2.88/0.93  --pure_diseq_elim                       true
% 2.88/0.93  --brand_transform                       false
% 2.88/0.93  --non_eq_to_eq                          false
% 2.88/0.93  --prep_def_merge                        true
% 2.88/0.93  --prep_def_merge_prop_impl              false
% 2.88/0.93  --prep_def_merge_mbd                    true
% 2.88/0.93  --prep_def_merge_tr_red                 false
% 2.88/0.93  --prep_def_merge_tr_cl                  false
% 2.88/0.93  --smt_preprocessing                     true
% 2.88/0.93  --smt_ac_axioms                         fast
% 2.88/0.93  --preprocessed_out                      false
% 2.88/0.93  --preprocessed_stats                    false
% 2.88/0.93  
% 2.88/0.93  ------ Abstraction refinement Options
% 2.88/0.93  
% 2.88/0.93  --abstr_ref                             []
% 2.88/0.93  --abstr_ref_prep                        false
% 2.88/0.93  --abstr_ref_until_sat                   false
% 2.88/0.93  --abstr_ref_sig_restrict                funpre
% 2.88/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.93  --abstr_ref_under                       []
% 2.88/0.93  
% 2.88/0.93  ------ SAT Options
% 2.88/0.93  
% 2.88/0.93  --sat_mode                              false
% 2.88/0.93  --sat_fm_restart_options                ""
% 2.88/0.93  --sat_gr_def                            false
% 2.88/0.93  --sat_epr_types                         true
% 2.88/0.93  --sat_non_cyclic_types                  false
% 2.88/0.93  --sat_finite_models                     false
% 2.88/0.93  --sat_fm_lemmas                         false
% 2.88/0.93  --sat_fm_prep                           false
% 2.88/0.93  --sat_fm_uc_incr                        true
% 2.88/0.93  --sat_out_model                         small
% 2.88/0.93  --sat_out_clauses                       false
% 2.88/0.93  
% 2.88/0.93  ------ QBF Options
% 2.88/0.93  
% 2.88/0.93  --qbf_mode                              false
% 2.88/0.93  --qbf_elim_univ                         false
% 2.88/0.93  --qbf_dom_inst                          none
% 2.88/0.93  --qbf_dom_pre_inst                      false
% 2.88/0.93  --qbf_sk_in                             false
% 2.88/0.93  --qbf_pred_elim                         true
% 2.88/0.93  --qbf_split                             512
% 2.88/0.93  
% 2.88/0.93  ------ BMC1 Options
% 2.88/0.93  
% 2.88/0.93  --bmc1_incremental                      false
% 2.88/0.93  --bmc1_axioms                           reachable_all
% 2.88/0.93  --bmc1_min_bound                        0
% 2.88/0.93  --bmc1_max_bound                        -1
% 2.88/0.93  --bmc1_max_bound_default                -1
% 2.88/0.93  --bmc1_symbol_reachability              true
% 2.88/0.93  --bmc1_property_lemmas                  false
% 2.88/0.93  --bmc1_k_induction                      false
% 2.88/0.93  --bmc1_non_equiv_states                 false
% 2.88/0.93  --bmc1_deadlock                         false
% 2.88/0.93  --bmc1_ucm                              false
% 2.88/0.93  --bmc1_add_unsat_core                   none
% 2.88/0.93  --bmc1_unsat_core_children              false
% 2.88/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.93  --bmc1_out_stat                         full
% 2.88/0.93  --bmc1_ground_init                      false
% 2.88/0.93  --bmc1_pre_inst_next_state              false
% 2.88/0.93  --bmc1_pre_inst_state                   false
% 2.88/0.93  --bmc1_pre_inst_reach_state             false
% 2.88/0.93  --bmc1_out_unsat_core                   false
% 2.88/0.93  --bmc1_aig_witness_out                  false
% 2.88/0.93  --bmc1_verbose                          false
% 2.88/0.93  --bmc1_dump_clauses_tptp                false
% 2.88/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.93  --bmc1_dump_file                        -
% 2.88/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.93  --bmc1_ucm_extend_mode                  1
% 2.88/0.93  --bmc1_ucm_init_mode                    2
% 2.88/0.93  --bmc1_ucm_cone_mode                    none
% 2.88/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.93  --bmc1_ucm_relax_model                  4
% 2.88/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.93  --bmc1_ucm_layered_model                none
% 2.88/0.93  --bmc1_ucm_max_lemma_size               10
% 2.88/0.93  
% 2.88/0.93  ------ AIG Options
% 2.88/0.93  
% 2.88/0.93  --aig_mode                              false
% 2.88/0.93  
% 2.88/0.93  ------ Instantiation Options
% 2.88/0.93  
% 2.88/0.93  --instantiation_flag                    true
% 2.88/0.93  --inst_sos_flag                         false
% 2.88/0.93  --inst_sos_phase                        true
% 2.88/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.93  --inst_lit_sel_side                     num_symb
% 2.88/0.93  --inst_solver_per_active                1400
% 2.88/0.93  --inst_solver_calls_frac                1.
% 2.88/0.93  --inst_passive_queue_type               priority_queues
% 2.88/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.93  --inst_passive_queues_freq              [25;2]
% 2.88/0.93  --inst_dismatching                      true
% 2.88/0.93  --inst_eager_unprocessed_to_passive     true
% 2.88/0.93  --inst_prop_sim_given                   true
% 2.88/0.93  --inst_prop_sim_new                     false
% 2.88/0.93  --inst_subs_new                         false
% 2.88/0.93  --inst_eq_res_simp                      false
% 2.88/0.93  --inst_subs_given                       false
% 2.88/0.93  --inst_orphan_elimination               true
% 2.88/0.93  --inst_learning_loop_flag               true
% 2.88/0.93  --inst_learning_start                   3000
% 2.88/0.93  --inst_learning_factor                  2
% 2.88/0.93  --inst_start_prop_sim_after_learn       3
% 2.88/0.93  --inst_sel_renew                        solver
% 2.88/0.93  --inst_lit_activity_flag                true
% 2.88/0.93  --inst_restr_to_given                   false
% 2.88/0.93  --inst_activity_threshold               500
% 2.88/0.93  --inst_out_proof                        true
% 2.88/0.93  
% 2.88/0.93  ------ Resolution Options
% 2.88/0.93  
% 2.88/0.93  --resolution_flag                       true
% 2.88/0.93  --res_lit_sel                           adaptive
% 2.88/0.93  --res_lit_sel_side                      none
% 2.88/0.93  --res_ordering                          kbo
% 2.88/0.93  --res_to_prop_solver                    active
% 2.88/0.93  --res_prop_simpl_new                    false
% 2.88/0.93  --res_prop_simpl_given                  true
% 2.88/0.93  --res_passive_queue_type                priority_queues
% 2.88/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.93  --res_passive_queues_freq               [15;5]
% 2.88/0.93  --res_forward_subs                      full
% 2.88/0.93  --res_backward_subs                     full
% 2.88/0.93  --res_forward_subs_resolution           true
% 2.88/0.93  --res_backward_subs_resolution          true
% 2.88/0.93  --res_orphan_elimination                true
% 2.88/0.93  --res_time_limit                        2.
% 2.88/0.93  --res_out_proof                         true
% 2.88/0.93  
% 2.88/0.93  ------ Superposition Options
% 2.88/0.93  
% 2.88/0.93  --superposition_flag                    true
% 2.88/0.93  --sup_passive_queue_type                priority_queues
% 2.88/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.93  --demod_completeness_check              fast
% 2.88/0.93  --demod_use_ground                      true
% 2.88/0.93  --sup_to_prop_solver                    passive
% 2.88/0.93  --sup_prop_simpl_new                    true
% 2.88/0.93  --sup_prop_simpl_given                  true
% 2.88/0.93  --sup_fun_splitting                     false
% 2.88/0.93  --sup_smt_interval                      50000
% 2.88/0.93  
% 2.88/0.93  ------ Superposition Simplification Setup
% 2.88/0.93  
% 2.88/0.93  --sup_indices_passive                   []
% 2.88/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_full_bw                           [BwDemod]
% 2.88/0.93  --sup_immed_triv                        [TrivRules]
% 2.88/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_immed_bw_main                     []
% 2.88/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.93  
% 2.88/0.93  ------ Combination Options
% 2.88/0.93  
% 2.88/0.93  --comb_res_mult                         3
% 2.88/0.93  --comb_sup_mult                         2
% 2.88/0.93  --comb_inst_mult                        10
% 2.88/0.93  
% 2.88/0.93  ------ Debug Options
% 2.88/0.93  
% 2.88/0.93  --dbg_backtrace                         false
% 2.88/0.93  --dbg_dump_prop_clauses                 false
% 2.88/0.93  --dbg_dump_prop_clauses_file            -
% 2.88/0.93  --dbg_out_stat                          false
% 2.88/0.93  ------ Parsing...
% 2.88/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.93  ------ Proving...
% 2.88/0.93  ------ Problem Properties 
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  clauses                                 31
% 2.88/0.93  conjectures                             2
% 2.88/0.93  EPR                                     14
% 2.88/0.93  Horn                                    26
% 2.88/0.93  unary                                   6
% 2.88/0.93  binary                                  8
% 2.88/0.93  lits                                    78
% 2.88/0.93  lits eq                                 13
% 2.88/0.93  fd_pure                                 0
% 2.88/0.93  fd_pseudo                               0
% 2.88/0.93  fd_cond                                 4
% 2.88/0.93  fd_pseudo_cond                          3
% 2.88/0.93  AC symbols                              0
% 2.88/0.93  
% 2.88/0.93  ------ Schedule dynamic 5 is on 
% 2.88/0.93  
% 2.88/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  ------ 
% 2.88/0.93  Current options:
% 2.88/0.93  ------ 
% 2.88/0.93  
% 2.88/0.93  ------ Input Options
% 2.88/0.93  
% 2.88/0.93  --out_options                           all
% 2.88/0.93  --tptp_safe_out                         true
% 2.88/0.93  --problem_path                          ""
% 2.88/0.93  --include_path                          ""
% 2.88/0.93  --clausifier                            res/vclausify_rel
% 2.88/0.93  --clausifier_options                    --mode clausify
% 2.88/0.93  --stdin                                 false
% 2.88/0.93  --stats_out                             all
% 2.88/0.93  
% 2.88/0.93  ------ General Options
% 2.88/0.93  
% 2.88/0.93  --fof                                   false
% 2.88/0.93  --time_out_real                         305.
% 2.88/0.93  --time_out_virtual                      -1.
% 2.88/0.93  --symbol_type_check                     false
% 2.88/0.93  --clausify_out                          false
% 2.88/0.93  --sig_cnt_out                           false
% 2.88/0.93  --trig_cnt_out                          false
% 2.88/0.93  --trig_cnt_out_tolerance                1.
% 2.88/0.93  --trig_cnt_out_sk_spl                   false
% 2.88/0.93  --abstr_cl_out                          false
% 2.88/0.93  
% 2.88/0.93  ------ Global Options
% 2.88/0.93  
% 2.88/0.93  --schedule                              default
% 2.88/0.93  --add_important_lit                     false
% 2.88/0.93  --prop_solver_per_cl                    1000
% 2.88/0.93  --min_unsat_core                        false
% 2.88/0.93  --soft_assumptions                      false
% 2.88/0.93  --soft_lemma_size                       3
% 2.88/0.93  --prop_impl_unit_size                   0
% 2.88/0.93  --prop_impl_unit                        []
% 2.88/0.93  --share_sel_clauses                     true
% 2.88/0.93  --reset_solvers                         false
% 2.88/0.93  --bc_imp_inh                            [conj_cone]
% 2.88/0.93  --conj_cone_tolerance                   3.
% 2.88/0.93  --extra_neg_conj                        none
% 2.88/0.93  --large_theory_mode                     true
% 2.88/0.93  --prolific_symb_bound                   200
% 2.88/0.93  --lt_threshold                          2000
% 2.88/0.93  --clause_weak_htbl                      true
% 2.88/0.93  --gc_record_bc_elim                     false
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing Options
% 2.88/0.93  
% 2.88/0.93  --preprocessing_flag                    true
% 2.88/0.93  --time_out_prep_mult                    0.1
% 2.88/0.93  --splitting_mode                        input
% 2.88/0.93  --splitting_grd                         true
% 2.88/0.93  --splitting_cvd                         false
% 2.88/0.93  --splitting_cvd_svl                     false
% 2.88/0.93  --splitting_nvd                         32
% 2.88/0.93  --sub_typing                            true
% 2.88/0.93  --prep_gs_sim                           true
% 2.88/0.93  --prep_unflatten                        true
% 2.88/0.93  --prep_res_sim                          true
% 2.88/0.93  --prep_upred                            true
% 2.88/0.93  --prep_sem_filter                       exhaustive
% 2.88/0.93  --prep_sem_filter_out                   false
% 2.88/0.93  --pred_elim                             true
% 2.88/0.93  --res_sim_input                         true
% 2.88/0.93  --eq_ax_congr_red                       true
% 2.88/0.93  --pure_diseq_elim                       true
% 2.88/0.93  --brand_transform                       false
% 2.88/0.93  --non_eq_to_eq                          false
% 2.88/0.93  --prep_def_merge                        true
% 2.88/0.93  --prep_def_merge_prop_impl              false
% 2.88/0.93  --prep_def_merge_mbd                    true
% 2.88/0.93  --prep_def_merge_tr_red                 false
% 2.88/0.93  --prep_def_merge_tr_cl                  false
% 2.88/0.93  --smt_preprocessing                     true
% 2.88/0.93  --smt_ac_axioms                         fast
% 2.88/0.93  --preprocessed_out                      false
% 2.88/0.93  --preprocessed_stats                    false
% 2.88/0.93  
% 2.88/0.93  ------ Abstraction refinement Options
% 2.88/0.93  
% 2.88/0.93  --abstr_ref                             []
% 2.88/0.93  --abstr_ref_prep                        false
% 2.88/0.93  --abstr_ref_until_sat                   false
% 2.88/0.93  --abstr_ref_sig_restrict                funpre
% 2.88/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.93  --abstr_ref_under                       []
% 2.88/0.93  
% 2.88/0.93  ------ SAT Options
% 2.88/0.93  
% 2.88/0.93  --sat_mode                              false
% 2.88/0.93  --sat_fm_restart_options                ""
% 2.88/0.93  --sat_gr_def                            false
% 2.88/0.93  --sat_epr_types                         true
% 2.88/0.93  --sat_non_cyclic_types                  false
% 2.88/0.93  --sat_finite_models                     false
% 2.88/0.93  --sat_fm_lemmas                         false
% 2.88/0.93  --sat_fm_prep                           false
% 2.88/0.93  --sat_fm_uc_incr                        true
% 2.88/0.93  --sat_out_model                         small
% 2.88/0.93  --sat_out_clauses                       false
% 2.88/0.93  
% 2.88/0.93  ------ QBF Options
% 2.88/0.93  
% 2.88/0.93  --qbf_mode                              false
% 2.88/0.93  --qbf_elim_univ                         false
% 2.88/0.93  --qbf_dom_inst                          none
% 2.88/0.93  --qbf_dom_pre_inst                      false
% 2.88/0.93  --qbf_sk_in                             false
% 2.88/0.93  --qbf_pred_elim                         true
% 2.88/0.93  --qbf_split                             512
% 2.88/0.93  
% 2.88/0.93  ------ BMC1 Options
% 2.88/0.93  
% 2.88/0.93  --bmc1_incremental                      false
% 2.88/0.93  --bmc1_axioms                           reachable_all
% 2.88/0.93  --bmc1_min_bound                        0
% 2.88/0.93  --bmc1_max_bound                        -1
% 2.88/0.93  --bmc1_max_bound_default                -1
% 2.88/0.93  --bmc1_symbol_reachability              true
% 2.88/0.93  --bmc1_property_lemmas                  false
% 2.88/0.93  --bmc1_k_induction                      false
% 2.88/0.93  --bmc1_non_equiv_states                 false
% 2.88/0.93  --bmc1_deadlock                         false
% 2.88/0.93  --bmc1_ucm                              false
% 2.88/0.93  --bmc1_add_unsat_core                   none
% 2.88/0.93  --bmc1_unsat_core_children              false
% 2.88/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.93  --bmc1_out_stat                         full
% 2.88/0.93  --bmc1_ground_init                      false
% 2.88/0.93  --bmc1_pre_inst_next_state              false
% 2.88/0.93  --bmc1_pre_inst_state                   false
% 2.88/0.93  --bmc1_pre_inst_reach_state             false
% 2.88/0.93  --bmc1_out_unsat_core                   false
% 2.88/0.93  --bmc1_aig_witness_out                  false
% 2.88/0.93  --bmc1_verbose                          false
% 2.88/0.93  --bmc1_dump_clauses_tptp                false
% 2.88/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.93  --bmc1_dump_file                        -
% 2.88/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.93  --bmc1_ucm_extend_mode                  1
% 2.88/0.93  --bmc1_ucm_init_mode                    2
% 2.88/0.93  --bmc1_ucm_cone_mode                    none
% 2.88/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.93  --bmc1_ucm_relax_model                  4
% 2.88/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.93  --bmc1_ucm_layered_model                none
% 2.88/0.93  --bmc1_ucm_max_lemma_size               10
% 2.88/0.93  
% 2.88/0.93  ------ AIG Options
% 2.88/0.93  
% 2.88/0.93  --aig_mode                              false
% 2.88/0.93  
% 2.88/0.93  ------ Instantiation Options
% 2.88/0.93  
% 2.88/0.93  --instantiation_flag                    true
% 2.88/0.93  --inst_sos_flag                         false
% 2.88/0.93  --inst_sos_phase                        true
% 2.88/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.93  --inst_lit_sel_side                     none
% 2.88/0.93  --inst_solver_per_active                1400
% 2.88/0.93  --inst_solver_calls_frac                1.
% 2.88/0.93  --inst_passive_queue_type               priority_queues
% 2.88/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.93  --inst_passive_queues_freq              [25;2]
% 2.88/0.93  --inst_dismatching                      true
% 2.88/0.93  --inst_eager_unprocessed_to_passive     true
% 2.88/0.93  --inst_prop_sim_given                   true
% 2.88/0.93  --inst_prop_sim_new                     false
% 2.88/0.93  --inst_subs_new                         false
% 2.88/0.93  --inst_eq_res_simp                      false
% 2.88/0.93  --inst_subs_given                       false
% 2.88/0.93  --inst_orphan_elimination               true
% 2.88/0.93  --inst_learning_loop_flag               true
% 2.88/0.93  --inst_learning_start                   3000
% 2.88/0.93  --inst_learning_factor                  2
% 2.88/0.93  --inst_start_prop_sim_after_learn       3
% 2.88/0.93  --inst_sel_renew                        solver
% 2.88/0.93  --inst_lit_activity_flag                true
% 2.88/0.93  --inst_restr_to_given                   false
% 2.88/0.93  --inst_activity_threshold               500
% 2.88/0.93  --inst_out_proof                        true
% 2.88/0.93  
% 2.88/0.93  ------ Resolution Options
% 2.88/0.93  
% 2.88/0.93  --resolution_flag                       false
% 2.88/0.93  --res_lit_sel                           adaptive
% 2.88/0.93  --res_lit_sel_side                      none
% 2.88/0.93  --res_ordering                          kbo
% 2.88/0.93  --res_to_prop_solver                    active
% 2.88/0.93  --res_prop_simpl_new                    false
% 2.88/0.93  --res_prop_simpl_given                  true
% 2.88/0.93  --res_passive_queue_type                priority_queues
% 2.88/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.93  --res_passive_queues_freq               [15;5]
% 2.88/0.93  --res_forward_subs                      full
% 2.88/0.93  --res_backward_subs                     full
% 2.88/0.93  --res_forward_subs_resolution           true
% 2.88/0.93  --res_backward_subs_resolution          true
% 2.88/0.93  --res_orphan_elimination                true
% 2.88/0.93  --res_time_limit                        2.
% 2.88/0.93  --res_out_proof                         true
% 2.88/0.93  
% 2.88/0.93  ------ Superposition Options
% 2.88/0.93  
% 2.88/0.93  --superposition_flag                    true
% 2.88/0.93  --sup_passive_queue_type                priority_queues
% 2.88/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.93  --demod_completeness_check              fast
% 2.88/0.93  --demod_use_ground                      true
% 2.88/0.93  --sup_to_prop_solver                    passive
% 2.88/0.93  --sup_prop_simpl_new                    true
% 2.88/0.93  --sup_prop_simpl_given                  true
% 2.88/0.93  --sup_fun_splitting                     false
% 2.88/0.93  --sup_smt_interval                      50000
% 2.88/0.93  
% 2.88/0.93  ------ Superposition Simplification Setup
% 2.88/0.93  
% 2.88/0.93  --sup_indices_passive                   []
% 2.88/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_full_bw                           [BwDemod]
% 2.88/0.93  --sup_immed_triv                        [TrivRules]
% 2.88/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_immed_bw_main                     []
% 2.88/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.93  
% 2.88/0.93  ------ Combination Options
% 2.88/0.93  
% 2.88/0.93  --comb_res_mult                         3
% 2.88/0.93  --comb_sup_mult                         2
% 2.88/0.93  --comb_inst_mult                        10
% 2.88/0.93  
% 2.88/0.93  ------ Debug Options
% 2.88/0.93  
% 2.88/0.93  --dbg_backtrace                         false
% 2.88/0.93  --dbg_dump_prop_clauses                 false
% 2.88/0.93  --dbg_dump_prop_clauses_file            -
% 2.88/0.93  --dbg_out_stat                          false
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  ------ Proving...
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  % SZS status Theorem for theBenchmark.p
% 2.88/0.93  
% 2.88/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.93  
% 2.88/0.93  fof(f5,axiom,(
% 2.88/0.93    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f75,plain,(
% 2.88/0.93    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.88/0.93    inference(cnf_transformation,[],[f5])).
% 2.88/0.93  
% 2.88/0.93  fof(f4,axiom,(
% 2.88/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f27,plain,(
% 2.88/0.93    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.88/0.93    inference(ennf_transformation,[],[f4])).
% 2.88/0.93  
% 2.88/0.93  fof(f74,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.88/0.93    inference(cnf_transformation,[],[f27])).
% 2.88/0.93  
% 2.88/0.93  fof(f9,axiom,(
% 2.88/0.93    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f82,plain,(
% 2.88/0.93    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.88/0.93    inference(cnf_transformation,[],[f9])).
% 2.88/0.93  
% 2.88/0.93  fof(f10,axiom,(
% 2.88/0.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f56,plain,(
% 2.88/0.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.88/0.93    inference(nnf_transformation,[],[f10])).
% 2.88/0.93  
% 2.88/0.93  fof(f83,plain,(
% 2.88/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.88/0.93    inference(cnf_transformation,[],[f56])).
% 2.88/0.93  
% 2.88/0.93  fof(f3,axiom,(
% 2.88/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f53,plain,(
% 2.88/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/0.93    inference(nnf_transformation,[],[f3])).
% 2.88/0.93  
% 2.88/0.93  fof(f54,plain,(
% 2.88/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/0.93    inference(flattening,[],[f53])).
% 2.88/0.93  
% 2.88/0.93  fof(f73,plain,(
% 2.88/0.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f54])).
% 2.88/0.93  
% 2.88/0.93  fof(f6,axiom,(
% 2.88/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f25,plain,(
% 2.88/0.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 2.88/0.93    inference(unused_predicate_definition_removal,[],[f6])).
% 2.88/0.93  
% 2.88/0.93  fof(f28,plain,(
% 2.88/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 2.88/0.93    inference(ennf_transformation,[],[f25])).
% 2.88/0.93  
% 2.88/0.93  fof(f76,plain,(
% 2.88/0.93    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.88/0.93    inference(cnf_transformation,[],[f28])).
% 2.88/0.93  
% 2.88/0.93  fof(f20,axiom,(
% 2.88/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f45,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f20])).
% 2.88/0.93  
% 2.88/0.93  fof(f46,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f45])).
% 2.88/0.93  
% 2.88/0.93  fof(f96,plain,(
% 2.88/0.93    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f46])).
% 2.88/0.93  
% 2.88/0.93  fof(f22,conjecture,(
% 2.88/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f23,negated_conjecture,(
% 2.88/0.93    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.88/0.93    inference(negated_conjecture,[],[f22])).
% 2.88/0.93  
% 2.88/0.93  fof(f49,plain,(
% 2.88/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f23])).
% 2.88/0.93  
% 2.88/0.93  fof(f50,plain,(
% 2.88/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f49])).
% 2.88/0.93  
% 2.88/0.93  fof(f60,plain,(
% 2.88/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.88/0.93    inference(nnf_transformation,[],[f50])).
% 2.88/0.93  
% 2.88/0.93  fof(f61,plain,(
% 2.88/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f60])).
% 2.88/0.93  
% 2.88/0.93  fof(f65,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 2.88/0.93    introduced(choice_axiom,[])).
% 2.88/0.93  
% 2.88/0.93  fof(f64,plain,(
% 2.88/0.93    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 2.88/0.93    introduced(choice_axiom,[])).
% 2.88/0.93  
% 2.88/0.93  fof(f63,plain,(
% 2.88/0.93    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 2.88/0.93    introduced(choice_axiom,[])).
% 2.88/0.93  
% 2.88/0.93  fof(f62,plain,(
% 2.88/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.88/0.93    introduced(choice_axiom,[])).
% 2.88/0.93  
% 2.88/0.93  fof(f66,plain,(
% 2.88/0.93    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.88/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f61,f65,f64,f63,f62])).
% 2.88/0.93  
% 2.88/0.93  fof(f104,plain,(
% 2.88/0.93    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f103,plain,(
% 2.88/0.93    l1_orders_2(sK1)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f99,plain,(
% 2.88/0.93    ~v2_struct_0(sK1)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f100,plain,(
% 2.88/0.93    v3_orders_2(sK1)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f101,plain,(
% 2.88/0.93    v4_orders_2(sK1)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f102,plain,(
% 2.88/0.93    v5_orders_2(sK1)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f1,axiom,(
% 2.88/0.93    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f51,plain,(
% 2.88/0.93    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.88/0.93    inference(nnf_transformation,[],[f1])).
% 2.88/0.93  
% 2.88/0.93  fof(f52,plain,(
% 2.88/0.93    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.88/0.93    inference(flattening,[],[f51])).
% 2.88/0.93  
% 2.88/0.93  fof(f68,plain,(
% 2.88/0.93    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f52])).
% 2.88/0.93  
% 2.88/0.93  fof(f109,plain,(
% 2.88/0.93    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.88/0.93    inference(equality_resolution,[],[f68])).
% 2.88/0.93  
% 2.88/0.93  fof(f107,plain,(
% 2.88/0.93    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f105,plain,(
% 2.88/0.93    m2_orders_2(sK3,sK1,sK2)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f106,plain,(
% 2.88/0.93    m2_orders_2(sK4,sK1,sK2)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f21,axiom,(
% 2.88/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f47,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f21])).
% 2.88/0.93  
% 2.88/0.93  fof(f48,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f47])).
% 2.88/0.93  
% 2.88/0.93  fof(f59,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(nnf_transformation,[],[f48])).
% 2.88/0.93  
% 2.88/0.93  fof(f98,plain,(
% 2.88/0.93    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f59])).
% 2.88/0.93  
% 2.88/0.93  fof(f69,plain,(
% 2.88/0.93    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f52])).
% 2.88/0.93  
% 2.88/0.93  fof(f108,plain,(
% 2.88/0.93    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 2.88/0.93    inference(cnf_transformation,[],[f66])).
% 2.88/0.93  
% 2.88/0.93  fof(f17,axiom,(
% 2.88/0.93    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f26,plain,(
% 2.88/0.93    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.88/0.93    inference(pure_predicate_removal,[],[f17])).
% 2.88/0.93  
% 2.88/0.93  fof(f39,plain,(
% 2.88/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f26])).
% 2.88/0.93  
% 2.88/0.93  fof(f40,plain,(
% 2.88/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f39])).
% 2.88/0.93  
% 2.88/0.93  fof(f93,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f40])).
% 2.88/0.93  
% 2.88/0.93  fof(f18,axiom,(
% 2.88/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f41,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f18])).
% 2.88/0.93  
% 2.88/0.93  fof(f42,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f41])).
% 2.88/0.93  
% 2.88/0.93  fof(f94,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f42])).
% 2.88/0.93  
% 2.88/0.93  fof(f97,plain,(
% 2.88/0.93    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f59])).
% 2.88/0.93  
% 2.88/0.93  fof(f16,axiom,(
% 2.88/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f37,plain,(
% 2.88/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f16])).
% 2.88/0.93  
% 2.88/0.93  fof(f38,plain,(
% 2.88/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f37])).
% 2.88/0.93  
% 2.88/0.93  fof(f92,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f38])).
% 2.88/0.93  
% 2.88/0.93  fof(f67,plain,(
% 2.88/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f52])).
% 2.88/0.93  
% 2.88/0.93  fof(f19,axiom,(
% 2.88/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.88/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.93  
% 2.88/0.93  fof(f43,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/0.93    inference(ennf_transformation,[],[f19])).
% 2.88/0.93  
% 2.88/0.93  fof(f44,plain,(
% 2.88/0.93    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/0.93    inference(flattening,[],[f43])).
% 2.88/0.93  
% 2.88/0.93  fof(f95,plain,(
% 2.88/0.93    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/0.93    inference(cnf_transformation,[],[f44])).
% 2.88/0.93  
% 2.88/0.93  cnf(c_8,plain,
% 2.88/0.93      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 2.88/0.93      inference(cnf_transformation,[],[f75]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2407,plain,
% 2.88/0.93      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_7,plain,
% 2.88/0.93      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 2.88/0.93      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 2.88/0.93      inference(cnf_transformation,[],[f74]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2408,plain,
% 2.88/0.93      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 2.88/0.93      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4548,plain,
% 2.88/0.93      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2407,c_2408]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_15,plain,
% 2.88/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.88/0.93      inference(cnf_transformation,[],[f82]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2402,plain,
% 2.88/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_17,plain,
% 2.88/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f83]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2400,plain,
% 2.88/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.88/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_3958,plain,
% 2.88/0.93      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2402,c_2400]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4,plain,
% 2.88/0.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.88/0.93      inference(cnf_transformation,[],[f73]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2410,plain,
% 2.88/0.93      ( X0 = X1
% 2.88/0.93      | r1_tarski(X0,X1) != iProver_top
% 2.88/0.93      | r1_tarski(X1,X0) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_6503,plain,
% 2.88/0.93      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_3958,c_2410]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_7574,plain,
% 2.88/0.93      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_4548,c_6503]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_9,plain,
% 2.88/0.93      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.88/0.93      inference(cnf_transformation,[],[f76]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_29,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/0.93      | ~ r1_xboole_0(X0,X3)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f96]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_36,negated_conjecture,
% 2.88/0.93      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 2.88/0.93      inference(cnf_transformation,[],[f104]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_688,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | ~ r1_xboole_0(X0,X3)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK2 != X2 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_29,c_36]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_689,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | ~ r1_xboole_0(X2,X0)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_688]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_772,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X2 != X3
% 2.88/0.93      | X0 != X4
% 2.88/0.93      | k4_xboole_0(X3,X4) != X3
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_689]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_773,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k4_xboole_0(X0,X2) != X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_772]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_37,negated_conjecture,
% 2.88/0.93      ( l1_orders_2(sK1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f103]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1038,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | k4_xboole_0(X0,X2) != X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_773,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1039,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1)
% 2.88/0.93      | k4_xboole_0(X1,X0) != X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1038]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_41,negated_conjecture,
% 2.88/0.93      ( ~ v2_struct_0(sK1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f99]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_40,negated_conjecture,
% 2.88/0.93      ( v3_orders_2(sK1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f100]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_39,negated_conjecture,
% 2.88/0.93      ( v4_orders_2(sK1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f101]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_38,negated_conjecture,
% 2.88/0.93      ( v5_orders_2(sK1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f102]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1043,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | k4_xboole_0(X1,X0) != X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1039,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1282,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | k4_xboole_0(X1,X0) != X1 ),
% 2.88/0.93      inference(equality_resolution_simp,[status(thm)],[c_1043]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2381,plain,
% 2.88/0.93      ( k4_xboole_0(X0,X1) != X0
% 2.88/0.93      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_9973,plain,
% 2.88/0.93      ( k1_xboole_0 != X0 | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_7574,c_2381]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_9987,plain,
% 2.88/0.93      ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
% 2.88/0.93      inference(equality_resolution,[status(thm)],[c_9973]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1,plain,
% 2.88/0.93      ( ~ r2_xboole_0(X0,X0) ),
% 2.88/0.93      inference(cnf_transformation,[],[f109]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_33,negated_conjecture,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.88/0.93      inference(cnf_transformation,[],[f107]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_313,plain,
% 2.88/0.93      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 2.88/0.93      inference(prop_impl,[status(thm)],[c_33]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_314,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.88/0.93      inference(renaming,[status(thm)],[c_313]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_590,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_314]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_591,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_590]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2388,plain,
% 2.88/0.93      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_35,negated_conjecture,
% 2.88/0.93      ( m2_orders_2(sK3,sK1,sK2) ),
% 2.88/0.93      inference(cnf_transformation,[],[f105]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2391,plain,
% 2.88/0.93      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_34,negated_conjecture,
% 2.88/0.93      ( m2_orders_2(sK4,sK1,sK2) ),
% 2.88/0.93      inference(cnf_transformation,[],[f106]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2392,plain,
% 2.88/0.93      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_30,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | m1_orders_2(X3,X1,X0)
% 2.88/0.93      | m1_orders_2(X0,X1,X3)
% 2.88/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X3 = X0 ),
% 2.88/0.93      inference(cnf_transformation,[],[f98]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_649,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | m1_orders_2(X3,X1,X0)
% 2.88/0.93      | m1_orders_2(X0,X1,X3)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X3 = X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK2 != X2 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_650,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | m1_orders_2(X0,X1,X2)
% 2.88/0.93      | m1_orders_2(X2,X1,X0)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X0 = X2
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_649]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1083,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | m1_orders_2(X0,X1,X2)
% 2.88/0.93      | m1_orders_2(X2,X1,X0)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | X2 = X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_650,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1084,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1)
% 2.88/0.93      | X0 = X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1083]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1088,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | X0 = X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1084,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1274,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | X0 = X1 ),
% 2.88/0.93      inference(equality_resolution_simp,[status(thm)],[c_1088]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2383,plain,
% 2.88/0.93      ( X0 = X1
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) = iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_3784,plain,
% 2.88/0.93      ( sK4 = X0
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 2.88/0.93      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2392,c_2383]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4127,plain,
% 2.88/0.93      ( sK4 = sK3
% 2.88/0.93      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.88/0.93      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2391,c_3784]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_49,plain,
% 2.88/0.93      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_0,plain,
% 2.88/0.93      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.88/0.93      inference(cnf_transformation,[],[f69]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_32,negated_conjecture,
% 2.88/0.93      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.88/0.93      inference(cnf_transformation,[],[f108]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_311,plain,
% 2.88/0.93      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 2.88/0.93      inference(prop_impl,[status(thm)],[c_32]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_312,plain,
% 2.88/0.93      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.88/0.93      inference(renaming,[status(thm)],[c_311]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_567,plain,
% 2.88/0.93      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.88/0.93      | ~ r1_tarski(X0,X1)
% 2.88/0.93      | X1 = X0
% 2.88/0.93      | sK4 != X1
% 2.88/0.93      | sK3 != X0 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_312]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_568,plain,
% 2.88/0.93      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_567]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_569,plain,
% 2.88/0.93      ( sK4 = sK3
% 2.88/0.93      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.88/0.93      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_26,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f93]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_721,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK2 != X2 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_722,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_721]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1062,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_722,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1063,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1)
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1062]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1067,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1063,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1278,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.88/0.93      inference(equality_resolution_simp,[status(thm)],[c_1067]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2632,plain,
% 2.88/0.93      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.88/0.93      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.88/0.93      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2633,plain,
% 2.88/0.93      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_2632]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_27,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | r1_tarski(X0,X2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f94]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1167,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | r1_tarski(X0,X2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1168,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | r1_tarski(X0,X1)
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1167]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1170,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | r1_tarski(X0,X1) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1168,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2648,plain,
% 2.88/0.93      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.88/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | r1_tarski(sK3,sK4) ),
% 2.88/0.93      inference(instantiation,[status(thm)],[c_1170]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2649,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.88/0.93      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.88/0.93      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4136,plain,
% 2.88/0.93      ( m1_orders_2(sK4,sK1,sK3) = iProver_top | sK4 = sK3 ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_4127,c_49,c_569,c_2633,c_2649]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4137,plain,
% 2.88/0.93      ( sK4 = sK3 | m1_orders_2(sK4,sK1,sK3) = iProver_top ),
% 2.88/0.93      inference(renaming,[status(thm)],[c_4136]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_31,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X3,X1,X0)
% 2.88/0.93      | ~ m1_orders_2(X0,X1,X3)
% 2.88/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X3 = X0 ),
% 2.88/0.93      inference(cnf_transformation,[],[f97]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_610,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X3,X1,X0)
% 2.88/0.93      | ~ m1_orders_2(X0,X1,X3)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X3 = X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK2 != X2 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_611,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | X0 = X2
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_610]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1113,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,X1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X2,X1,sK2)
% 2.88/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | X2 = X0
% 2.88/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_611,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1114,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1)
% 2.88/0.93      | X0 = X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1113]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1118,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | X0 = X1
% 2.88/0.93      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1114,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1270,plain,
% 2.88/0.93      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.88/0.93      | ~ m2_orders_2(X1,sK1,sK2)
% 2.88/0.93      | ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | X0 = X1 ),
% 2.88/0.93      inference(equality_resolution_simp,[status(thm)],[c_1118]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2384,plain,
% 2.88/0.93      ( X0 = X1
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_123,plain,
% 2.88/0.93      ( X0 = X1
% 2.88/0.93      | r1_tarski(X0,X1) != iProver_top
% 2.88/0.93      | r1_tarski(X1,X0) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1172,plain,
% 2.88/0.93      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.88/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2382,plain,
% 2.88/0.93      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_25,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f92]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1184,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | sK1 != X1 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1185,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1184]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1187,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1185,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2385,plain,
% 2.88/0.93      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1187]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2713,plain,
% 2.88/0.93      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.88/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2382,c_2385]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2386,plain,
% 2.88/0.93      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.88/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2714,plain,
% 2.88/0.93      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.88/0.93      | r1_tarski(X1,X0) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2382,c_2386]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4516,plain,
% 2.88/0.93      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | X0 = X1
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_2384,c_123,c_1172,c_2713,c_2714]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4517,plain,
% 2.88/0.93      ( X0 = X1
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(renaming,[status(thm)],[c_4516]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4525,plain,
% 2.88/0.93      ( sK3 = X0
% 2.88/0.93      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 2.88/0.93      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2391,c_4517]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4909,plain,
% 2.88/0.93      ( sK4 = sK3 | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_4137,c_4525]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2,plain,
% 2.88/0.93      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.88/0.93      inference(cnf_transformation,[],[f67]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_580,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4)
% 2.88/0.93      | r1_tarski(X0,X1)
% 2.88/0.93      | sK4 != X1
% 2.88/0.93      | sK3 != X0 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_314]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_581,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_580]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_582,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 2.88/0.93      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_592,plain,
% 2.88/0.93      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_3088,plain,
% 2.88/0.93      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.88/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4081,plain,
% 2.88/0.93      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 2.88/0.93      inference(instantiation,[status(thm)],[c_3088]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4082,plain,
% 2.88/0.93      ( sK3 = sK4
% 2.88/0.93      | r1_tarski(sK4,sK3) != iProver_top
% 2.88/0.93      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_4081]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2755,plain,
% 2.88/0.93      ( m1_orders_2(X0,sK1,sK3) != iProver_top
% 2.88/0.93      | r1_tarski(X0,sK3) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2391,c_2714]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4144,plain,
% 2.88/0.93      ( sK4 = sK3 | r1_tarski(sK4,sK3) = iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_4137,c_2755]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_4912,plain,
% 2.88/0.93      ( sK4 = sK3 ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_4909,c_582,c_592,c_4082,c_4144]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5126,plain,
% 2.88/0.93      ( sK3 != sK3 | m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 2.88/0.93      inference(light_normalisation,[status(thm)],[c_2388,c_4912]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5127,plain,
% 2.88/0.93      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 2.88/0.93      inference(equality_resolution_simp,[status(thm)],[c_5126]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_28,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_xboole_0 = X2 ),
% 2.88/0.93      inference(cnf_transformation,[],[f95]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_228,plain,
% 2.88/0.93      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_xboole_0 = X2 ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_28,c_25]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_229,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | ~ l1_orders_2(X1)
% 2.88/0.93      | k1_xboole_0 = X2 ),
% 2.88/0.93      inference(renaming,[status(thm)],[c_228]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1143,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.88/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.88/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.88/0.93      | v2_struct_0(X1)
% 2.88/0.93      | ~ v3_orders_2(X1)
% 2.88/0.93      | ~ v4_orders_2(X1)
% 2.88/0.93      | ~ v5_orders_2(X1)
% 2.88/0.93      | sK1 != X1
% 2.88/0.93      | k1_xboole_0 = X2 ),
% 2.88/0.93      inference(resolution_lifted,[status(thm)],[c_229,c_37]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1144,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | v2_struct_0(sK1)
% 2.88/0.93      | ~ v3_orders_2(sK1)
% 2.88/0.93      | ~ v4_orders_2(sK1)
% 2.88/0.93      | ~ v5_orders_2(sK1)
% 2.88/0.93      | k1_xboole_0 = X0 ),
% 2.88/0.93      inference(unflattening,[status(thm)],[c_1143]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_1148,plain,
% 2.88/0.93      ( ~ m1_orders_2(X0,sK1,X1)
% 2.88/0.93      | ~ m1_orders_2(X1,sK1,X0)
% 2.88/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.88/0.93      | k1_xboole_0 = X0 ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_1144,c_41,c_40,c_39,c_38]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2387,plain,
% 2.88/0.93      ( k1_xboole_0 = X0
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.88/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.88/0.93      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_2712,plain,
% 2.88/0.93      ( k1_xboole_0 = X0
% 2.88/0.93      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.88/0.93      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.88/0.93      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2382,c_2387]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5495,plain,
% 2.88/0.93      ( sK3 = k1_xboole_0
% 2.88/0.93      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 2.88/0.93      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_2391,c_2712]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5503,plain,
% 2.88/0.93      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 2.88/0.93      inference(superposition,[status(thm)],[c_5127,c_5495]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5552,plain,
% 2.88/0.93      ( sK3 = k1_xboole_0 ),
% 2.88/0.93      inference(global_propositional_subsumption,
% 2.88/0.93                [status(thm)],
% 2.88/0.93                [c_5503,c_5127]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(c_5565,plain,
% 2.88/0.93      ( m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 2.88/0.93      inference(demodulation,[status(thm)],[c_5552,c_2391]) ).
% 2.88/0.93  
% 2.88/0.93  cnf(contradiction,plain,
% 2.88/0.93      ( $false ),
% 2.88/0.93      inference(minisat,[status(thm)],[c_9987,c_5565]) ).
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/0.93  
% 2.88/0.93  ------                               Statistics
% 2.88/0.93  
% 2.88/0.93  ------ General
% 2.88/0.93  
% 2.88/0.93  abstr_ref_over_cycles:                  0
% 2.88/0.93  abstr_ref_under_cycles:                 0
% 2.88/0.93  gc_basic_clause_elim:                   0
% 2.88/0.93  forced_gc_time:                         0
% 2.88/0.93  parsing_time:                           0.012
% 2.88/0.93  unif_index_cands_time:                  0.
% 2.88/0.93  unif_index_add_time:                    0.
% 2.88/0.93  orderings_time:                         0.
% 2.88/0.93  out_proof_time:                         0.021
% 2.88/0.93  total_time:                             0.357
% 2.88/0.93  num_of_symbols:                         58
% 2.88/0.93  num_of_terms:                           8324
% 2.88/0.93  
% 2.88/0.93  ------ Preprocessing
% 2.88/0.93  
% 2.88/0.93  num_of_splits:                          0
% 2.88/0.93  num_of_split_atoms:                     0
% 2.88/0.93  num_of_reused_defs:                     0
% 2.88/0.93  num_eq_ax_congr_red:                    35
% 2.88/0.93  num_of_sem_filtered_clauses:            1
% 2.88/0.93  num_of_subtypes:                        0
% 2.88/0.93  monotx_restored_types:                  0
% 2.88/0.93  sat_num_of_epr_types:                   0
% 2.88/0.93  sat_num_of_non_cyclic_types:            0
% 2.88/0.93  sat_guarded_non_collapsed_types:        0
% 2.88/0.93  num_pure_diseq_elim:                    0
% 2.88/0.93  simp_replaced_by:                       0
% 2.88/0.93  res_preprocessed:                       154
% 2.88/0.93  prep_upred:                             0
% 2.88/0.93  prep_unflattend:                        50
% 2.88/0.93  smt_new_axioms:                         0
% 2.88/0.93  pred_elim_cands:                        6
% 2.88/0.93  pred_elim:                              8
% 2.88/0.93  pred_elim_cl:                           9
% 2.88/0.93  pred_elim_cycles:                       12
% 2.88/0.93  merged_defs:                            10
% 2.88/0.93  merged_defs_ncl:                        0
% 2.88/0.93  bin_hyper_res:                          10
% 2.88/0.93  prep_cycles:                            4
% 2.88/0.93  pred_elim_time:                         0.017
% 2.88/0.93  splitting_time:                         0.
% 2.88/0.93  sem_filter_time:                        0.
% 2.88/0.93  monotx_time:                            0.002
% 2.88/0.93  subtype_inf_time:                       0.
% 2.88/0.93  
% 2.88/0.93  ------ Problem properties
% 2.88/0.93  
% 2.88/0.93  clauses:                                31
% 2.88/0.93  conjectures:                            2
% 2.88/0.93  epr:                                    14
% 2.88/0.93  horn:                                   26
% 2.88/0.93  ground:                                 5
% 2.88/0.93  unary:                                  6
% 2.88/0.93  binary:                                 8
% 2.88/0.93  lits:                                   78
% 2.88/0.93  lits_eq:                                13
% 2.88/0.93  fd_pure:                                0
% 2.88/0.93  fd_pseudo:                              0
% 2.88/0.93  fd_cond:                                4
% 2.88/0.93  fd_pseudo_cond:                         3
% 2.88/0.93  ac_symbols:                             0
% 2.88/0.93  
% 2.88/0.93  ------ Propositional Solver
% 2.88/0.93  
% 2.88/0.93  prop_solver_calls:                      28
% 2.88/0.93  prop_fast_solver_calls:                 1419
% 2.88/0.93  smt_solver_calls:                       0
% 2.88/0.93  smt_fast_solver_calls:                  0
% 2.88/0.93  prop_num_of_clauses:                    3979
% 2.88/0.93  prop_preprocess_simplified:             8996
% 2.88/0.93  prop_fo_subsumed:                       40
% 2.88/0.93  prop_solver_time:                       0.
% 2.88/0.93  smt_solver_time:                        0.
% 2.88/0.93  smt_fast_solver_time:                   0.
% 2.88/0.93  prop_fast_solver_time:                  0.
% 2.88/0.93  prop_unsat_core_time:                   0.
% 2.88/0.93  
% 2.88/0.93  ------ QBF
% 2.88/0.93  
% 2.88/0.93  qbf_q_res:                              0
% 2.88/0.93  qbf_num_tautologies:                    0
% 2.88/0.93  qbf_prep_cycles:                        0
% 2.88/0.93  
% 2.88/0.93  ------ BMC1
% 2.88/0.93  
% 2.88/0.93  bmc1_current_bound:                     -1
% 2.88/0.93  bmc1_last_solved_bound:                 -1
% 2.88/0.93  bmc1_unsat_core_size:                   -1
% 2.88/0.93  bmc1_unsat_core_parents_size:           -1
% 2.88/0.93  bmc1_merge_next_fun:                    0
% 2.88/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.88/0.93  
% 2.88/0.93  ------ Instantiation
% 2.88/0.93  
% 2.88/0.93  inst_num_of_clauses:                    1080
% 2.88/0.93  inst_num_in_passive:                    245
% 2.88/0.93  inst_num_in_active:                     476
% 2.88/0.93  inst_num_in_unprocessed:                360
% 2.88/0.93  inst_num_of_loops:                      550
% 2.88/0.93  inst_num_of_learning_restarts:          0
% 2.88/0.93  inst_num_moves_active_passive:          71
% 2.88/0.93  inst_lit_activity:                      0
% 2.88/0.93  inst_lit_activity_moves:                0
% 2.88/0.93  inst_num_tautologies:                   0
% 2.88/0.93  inst_num_prop_implied:                  0
% 2.88/0.93  inst_num_existing_simplified:           0
% 2.88/0.93  inst_num_eq_res_simplified:             0
% 2.88/0.93  inst_num_child_elim:                    0
% 2.88/0.93  inst_num_of_dismatching_blockings:      440
% 2.88/0.93  inst_num_of_non_proper_insts:           1125
% 2.88/0.93  inst_num_of_duplicates:                 0
% 2.88/0.93  inst_inst_num_from_inst_to_res:         0
% 2.88/0.93  inst_dismatching_checking_time:         0.
% 2.88/0.93  
% 2.88/0.93  ------ Resolution
% 2.88/0.93  
% 2.88/0.93  res_num_of_clauses:                     0
% 2.88/0.93  res_num_in_passive:                     0
% 2.88/0.93  res_num_in_active:                      0
% 2.88/0.93  res_num_of_loops:                       158
% 2.88/0.93  res_forward_subset_subsumed:            61
% 2.88/0.93  res_backward_subset_subsumed:           2
% 2.88/0.93  res_forward_subsumed:                   0
% 2.88/0.93  res_backward_subsumed:                  0
% 2.88/0.93  res_forward_subsumption_resolution:     0
% 2.88/0.93  res_backward_subsumption_resolution:    0
% 2.88/0.93  res_clause_to_clause_subsumption:       483
% 2.88/0.93  res_orphan_elimination:                 0
% 2.88/0.93  res_tautology_del:                      59
% 2.88/0.93  res_num_eq_res_simplified:              4
% 2.88/0.93  res_num_sel_changes:                    0
% 2.88/0.93  res_moves_from_active_to_pass:          0
% 2.88/0.93  
% 2.88/0.93  ------ Superposition
% 2.88/0.93  
% 2.88/0.93  sup_time_total:                         0.
% 2.88/0.93  sup_time_generating:                    0.
% 2.88/0.93  sup_time_sim_full:                      0.
% 2.88/0.93  sup_time_sim_immed:                     0.
% 2.88/0.93  
% 2.88/0.93  sup_num_of_clauses:                     121
% 2.88/0.93  sup_num_in_active:                      83
% 2.88/0.93  sup_num_in_passive:                     38
% 2.88/0.93  sup_num_of_loops:                       109
% 2.88/0.93  sup_fw_superposition:                   88
% 2.88/0.93  sup_bw_superposition:                   94
% 2.88/0.93  sup_immediate_simplified:               31
% 2.88/0.93  sup_given_eliminated:                   2
% 2.88/0.93  comparisons_done:                       0
% 2.88/0.93  comparisons_avoided:                    0
% 2.88/0.93  
% 2.88/0.93  ------ Simplifications
% 2.88/0.93  
% 2.88/0.93  
% 2.88/0.93  sim_fw_subset_subsumed:                 9
% 2.88/0.93  sim_bw_subset_subsumed:                 7
% 2.88/0.93  sim_fw_subsumed:                        18
% 2.88/0.93  sim_bw_subsumed:                        0
% 2.88/0.93  sim_fw_subsumption_res:                 5
% 2.88/0.93  sim_bw_subsumption_res:                 0
% 2.88/0.93  sim_tautology_del:                      3
% 2.88/0.93  sim_eq_tautology_del:                   13
% 2.88/0.93  sim_eq_res_simp:                        1
% 2.88/0.93  sim_fw_demodulated:                     0
% 2.88/0.93  sim_bw_demodulated:                     27
% 2.88/0.93  sim_light_normalised:                   11
% 2.88/0.93  sim_joinable_taut:                      0
% 2.88/0.93  sim_joinable_simp:                      0
% 2.88/0.93  sim_ac_normalised:                      0
% 2.88/0.93  sim_smt_subsumption:                    0
% 2.88/0.93  
%------------------------------------------------------------------------------
