%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:53 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  191 (5432 expanded)
%              Number of clauses        :  120 (1028 expanded)
%              Number of leaves         :   18 (1757 expanded)
%              Depth                    :   28
%              Number of atoms          :  888 (51883 expanded)
%              Number of equality atoms :  191 (1288 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_orders_2(X2,X0,X3)
            | ~ r2_xboole_0(X2,X3) )
          & ( m1_orders_2(X2,X0,X3)
            | r2_xboole_0(X2,X3) )
          & m2_orders_2(X3,X0,X1) )
     => ( ( ~ m1_orders_2(X2,X0,sK3)
          | ~ r2_xboole_0(X2,sK3) )
        & ( m1_orders_2(X2,X0,sK3)
          | r2_xboole_0(X2,sK3) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
            ( ( ~ m1_orders_2(sK2,X0,X3)
              | ~ r2_xboole_0(sK2,X3) )
            & ( m1_orders_2(sK2,X0,X3)
              | r2_xboole_0(sK2,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
                & m2_orders_2(X3,X0,sK1) )
            & m2_orders_2(X2,X0,sK1) )
        & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43,f42,f41])).

fof(f73,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1535,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1534,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1538,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2758,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1538])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1532,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2869,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2758,c_1532])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( ~ r2_xboole_0(X0,X1)
    | k4_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_374,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | k4_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_1529,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_3595,plain,
    ( k4_xboole_0(X0,X1) = X1
    | k1_xboole_0 != X1
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_1529])).

cnf(c_5153,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3595])).

cnf(c_5285,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1535,c_5153])).

cnf(c_5524,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5285,c_1534])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_218,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_219,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_423,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_219])).

cnf(c_424,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_1525,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_413,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_219])).

cnf(c_414,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_415,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_425,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2048,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2659,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_2660,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_22,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1530,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1531,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_489,plain,
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
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_490,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_657,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_490,c_24])).

cnf(c_658,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_662,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_28,c_27,c_26,c_25])).

cnf(c_839,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_662])).

cnf(c_1520,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_2610,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_1520])).

cnf(c_3120,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_2610])).

cnf(c_35,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_36,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2049,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_2747,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_2748,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2747])).

cnf(c_3129,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_35,c_36,c_425,c_2748])).

cnf(c_13,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_561,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_562,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_612,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_562,c_24])).

cnf(c_613,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_28,c_27,c_26,c_25])).

cnf(c_847,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_617])).

cnf(c_1518,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_741,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_742,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_744,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_28,c_27,c_26,c_25])).

cnf(c_1523,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1785,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1523])).

cnf(c_1906,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1785])).

cnf(c_3135,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_1906])).

cnf(c_4049,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_415,c_425,c_2660,c_3135])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_12])).

cnf(c_159,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_717,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_24])).

cnf(c_718,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_722,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_28,c_27,c_26,c_25])).

cnf(c_723,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_722])).

cnf(c_1524,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_1783,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1524])).

cnf(c_3847,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK0,sK3) != iProver_top
    | m1_orders_2(sK3,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_1783])).

cnf(c_4060,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_3847])).

cnf(c_1905,plain,
    ( m1_orders_2(X0,sK0,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_1785])).

cnf(c_4062,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_1905])).

cnf(c_1537,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4132,plain,
    ( sK3 = sK2
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4062,c_1537])).

cnf(c_19,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_216,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_217,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_390,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_217])).

cnf(c_391,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_392,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_1688,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_1689,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1688])).

cnf(c_1704,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_1705,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1704])).

cnf(c_4135,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4132,c_36,c_392,c_415,c_425,c_1689,c_1705,c_2660,c_3135])).

cnf(c_4248,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4060,c_4135])).

cnf(c_4249,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4248,c_4135])).

cnf(c_4145,plain,
    ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4135,c_3129])).

cnf(c_4253,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_4145])).

cnf(c_16,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_528,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_529,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_633,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_24])).

cnf(c_634,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_28,c_27,c_26,c_25])).

cnf(c_843,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_638])).

cnf(c_1519,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_1986,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1519])).

cnf(c_2347,plain,
    ( r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1986])).

cnf(c_4262,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4253,c_2347])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5524,c_4262])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:08:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.60/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/0.97  
% 2.60/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/0.97  
% 2.60/0.97  ------  iProver source info
% 2.60/0.97  
% 2.60/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.60/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/0.97  git: non_committed_changes: false
% 2.60/0.97  git: last_make_outside_of_git: false
% 2.60/0.97  
% 2.60/0.97  ------ 
% 2.60/0.97  
% 2.60/0.97  ------ Input Options
% 2.60/0.97  
% 2.60/0.97  --out_options                           all
% 2.60/0.97  --tptp_safe_out                         true
% 2.60/0.97  --problem_path                          ""
% 2.60/0.97  --include_path                          ""
% 2.60/0.97  --clausifier                            res/vclausify_rel
% 2.60/0.97  --clausifier_options                    --mode clausify
% 2.60/0.97  --stdin                                 false
% 2.60/0.97  --stats_out                             all
% 2.60/0.97  
% 2.60/0.97  ------ General Options
% 2.60/0.97  
% 2.60/0.97  --fof                                   false
% 2.60/0.97  --time_out_real                         305.
% 2.60/0.97  --time_out_virtual                      -1.
% 2.60/0.97  --symbol_type_check                     false
% 2.60/0.97  --clausify_out                          false
% 2.60/0.97  --sig_cnt_out                           false
% 2.60/0.97  --trig_cnt_out                          false
% 2.60/0.97  --trig_cnt_out_tolerance                1.
% 2.60/0.97  --trig_cnt_out_sk_spl                   false
% 2.60/0.97  --abstr_cl_out                          false
% 2.60/0.97  
% 2.60/0.97  ------ Global Options
% 2.60/0.97  
% 2.60/0.97  --schedule                              default
% 2.60/0.97  --add_important_lit                     false
% 2.60/0.97  --prop_solver_per_cl                    1000
% 2.60/0.97  --min_unsat_core                        false
% 2.60/0.97  --soft_assumptions                      false
% 2.60/0.97  --soft_lemma_size                       3
% 2.60/0.97  --prop_impl_unit_size                   0
% 2.60/0.97  --prop_impl_unit                        []
% 2.60/0.97  --share_sel_clauses                     true
% 2.60/0.97  --reset_solvers                         false
% 2.60/0.97  --bc_imp_inh                            [conj_cone]
% 2.60/0.97  --conj_cone_tolerance                   3.
% 2.60/0.97  --extra_neg_conj                        none
% 2.60/0.97  --large_theory_mode                     true
% 2.60/0.97  --prolific_symb_bound                   200
% 2.60/0.97  --lt_threshold                          2000
% 2.60/0.97  --clause_weak_htbl                      true
% 2.60/0.97  --gc_record_bc_elim                     false
% 2.60/0.97  
% 2.60/0.97  ------ Preprocessing Options
% 2.60/0.97  
% 2.60/0.97  --preprocessing_flag                    true
% 2.60/0.97  --time_out_prep_mult                    0.1
% 2.60/0.97  --splitting_mode                        input
% 2.60/0.97  --splitting_grd                         true
% 2.60/0.97  --splitting_cvd                         false
% 2.60/0.97  --splitting_cvd_svl                     false
% 2.60/0.97  --splitting_nvd                         32
% 2.60/0.97  --sub_typing                            true
% 2.60/0.97  --prep_gs_sim                           true
% 2.60/0.97  --prep_unflatten                        true
% 2.60/0.97  --prep_res_sim                          true
% 2.60/0.97  --prep_upred                            true
% 2.60/0.97  --prep_sem_filter                       exhaustive
% 2.60/0.97  --prep_sem_filter_out                   false
% 2.60/0.97  --pred_elim                             true
% 2.60/0.97  --res_sim_input                         true
% 2.60/0.97  --eq_ax_congr_red                       true
% 2.60/0.97  --pure_diseq_elim                       true
% 2.60/0.97  --brand_transform                       false
% 2.60/0.97  --non_eq_to_eq                          false
% 2.60/0.97  --prep_def_merge                        true
% 2.60/0.97  --prep_def_merge_prop_impl              false
% 2.60/0.97  --prep_def_merge_mbd                    true
% 2.60/0.97  --prep_def_merge_tr_red                 false
% 2.60/0.97  --prep_def_merge_tr_cl                  false
% 2.60/0.97  --smt_preprocessing                     true
% 2.60/0.97  --smt_ac_axioms                         fast
% 2.60/0.97  --preprocessed_out                      false
% 2.60/0.97  --preprocessed_stats                    false
% 2.60/0.97  
% 2.60/0.97  ------ Abstraction refinement Options
% 2.60/0.97  
% 2.60/0.97  --abstr_ref                             []
% 2.60/0.97  --abstr_ref_prep                        false
% 2.60/0.97  --abstr_ref_until_sat                   false
% 2.60/0.97  --abstr_ref_sig_restrict                funpre
% 2.60/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.97  --abstr_ref_under                       []
% 2.60/0.97  
% 2.60/0.97  ------ SAT Options
% 2.60/0.97  
% 2.60/0.97  --sat_mode                              false
% 2.60/0.97  --sat_fm_restart_options                ""
% 2.60/0.97  --sat_gr_def                            false
% 2.60/0.97  --sat_epr_types                         true
% 2.60/0.97  --sat_non_cyclic_types                  false
% 2.60/0.97  --sat_finite_models                     false
% 2.60/0.97  --sat_fm_lemmas                         false
% 2.60/0.97  --sat_fm_prep                           false
% 2.60/0.97  --sat_fm_uc_incr                        true
% 2.60/0.97  --sat_out_model                         small
% 2.60/0.97  --sat_out_clauses                       false
% 2.60/0.97  
% 2.60/0.97  ------ QBF Options
% 2.60/0.97  
% 2.60/0.97  --qbf_mode                              false
% 2.60/0.97  --qbf_elim_univ                         false
% 2.60/0.97  --qbf_dom_inst                          none
% 2.60/0.97  --qbf_dom_pre_inst                      false
% 2.60/0.97  --qbf_sk_in                             false
% 2.60/0.97  --qbf_pred_elim                         true
% 2.60/0.97  --qbf_split                             512
% 2.60/0.97  
% 2.60/0.97  ------ BMC1 Options
% 2.60/0.97  
% 2.60/0.97  --bmc1_incremental                      false
% 2.60/0.97  --bmc1_axioms                           reachable_all
% 2.60/0.97  --bmc1_min_bound                        0
% 2.60/0.97  --bmc1_max_bound                        -1
% 2.60/0.97  --bmc1_max_bound_default                -1
% 2.60/0.97  --bmc1_symbol_reachability              true
% 2.60/0.97  --bmc1_property_lemmas                  false
% 2.60/0.97  --bmc1_k_induction                      false
% 2.60/0.97  --bmc1_non_equiv_states                 false
% 2.60/0.97  --bmc1_deadlock                         false
% 2.60/0.97  --bmc1_ucm                              false
% 2.60/0.97  --bmc1_add_unsat_core                   none
% 2.60/0.97  --bmc1_unsat_core_children              false
% 2.60/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.97  --bmc1_out_stat                         full
% 2.60/0.97  --bmc1_ground_init                      false
% 2.60/0.97  --bmc1_pre_inst_next_state              false
% 2.60/0.97  --bmc1_pre_inst_state                   false
% 2.60/0.97  --bmc1_pre_inst_reach_state             false
% 2.60/0.97  --bmc1_out_unsat_core                   false
% 2.60/0.97  --bmc1_aig_witness_out                  false
% 2.60/0.97  --bmc1_verbose                          false
% 2.60/0.97  --bmc1_dump_clauses_tptp                false
% 2.60/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.97  --bmc1_dump_file                        -
% 2.60/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.97  --bmc1_ucm_extend_mode                  1
% 2.60/0.97  --bmc1_ucm_init_mode                    2
% 2.60/0.97  --bmc1_ucm_cone_mode                    none
% 2.60/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.97  --bmc1_ucm_relax_model                  4
% 2.60/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.97  --bmc1_ucm_layered_model                none
% 2.60/0.97  --bmc1_ucm_max_lemma_size               10
% 2.60/0.97  
% 2.60/0.97  ------ AIG Options
% 2.60/0.97  
% 2.60/0.97  --aig_mode                              false
% 2.60/0.97  
% 2.60/0.97  ------ Instantiation Options
% 2.60/0.97  
% 2.60/0.97  --instantiation_flag                    true
% 2.60/0.97  --inst_sos_flag                         false
% 2.60/0.97  --inst_sos_phase                        true
% 2.60/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.97  --inst_lit_sel_side                     num_symb
% 2.60/0.97  --inst_solver_per_active                1400
% 2.60/0.97  --inst_solver_calls_frac                1.
% 2.60/0.97  --inst_passive_queue_type               priority_queues
% 2.60/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.97  --inst_passive_queues_freq              [25;2]
% 2.60/0.97  --inst_dismatching                      true
% 2.60/0.97  --inst_eager_unprocessed_to_passive     true
% 2.60/0.97  --inst_prop_sim_given                   true
% 2.60/0.97  --inst_prop_sim_new                     false
% 2.60/0.97  --inst_subs_new                         false
% 2.60/0.97  --inst_eq_res_simp                      false
% 2.60/0.97  --inst_subs_given                       false
% 2.60/0.97  --inst_orphan_elimination               true
% 2.60/0.97  --inst_learning_loop_flag               true
% 2.60/0.97  --inst_learning_start                   3000
% 2.60/0.97  --inst_learning_factor                  2
% 2.60/0.97  --inst_start_prop_sim_after_learn       3
% 2.60/0.97  --inst_sel_renew                        solver
% 2.60/0.97  --inst_lit_activity_flag                true
% 2.60/0.97  --inst_restr_to_given                   false
% 2.60/0.97  --inst_activity_threshold               500
% 2.60/0.97  --inst_out_proof                        true
% 2.60/0.97  
% 2.60/0.97  ------ Resolution Options
% 2.60/0.97  
% 2.60/0.97  --resolution_flag                       true
% 2.60/0.97  --res_lit_sel                           adaptive
% 2.60/0.97  --res_lit_sel_side                      none
% 2.60/0.97  --res_ordering                          kbo
% 2.60/0.97  --res_to_prop_solver                    active
% 2.60/0.97  --res_prop_simpl_new                    false
% 2.60/0.97  --res_prop_simpl_given                  true
% 2.60/0.97  --res_passive_queue_type                priority_queues
% 2.60/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.97  --res_passive_queues_freq               [15;5]
% 2.60/0.97  --res_forward_subs                      full
% 2.60/0.97  --res_backward_subs                     full
% 2.60/0.97  --res_forward_subs_resolution           true
% 2.60/0.97  --res_backward_subs_resolution          true
% 2.60/0.97  --res_orphan_elimination                true
% 2.60/0.97  --res_time_limit                        2.
% 2.60/0.97  --res_out_proof                         true
% 2.60/0.97  
% 2.60/0.97  ------ Superposition Options
% 2.60/0.97  
% 2.60/0.97  --superposition_flag                    true
% 2.60/0.97  --sup_passive_queue_type                priority_queues
% 2.60/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.97  --demod_completeness_check              fast
% 2.60/0.97  --demod_use_ground                      true
% 2.60/0.97  --sup_to_prop_solver                    passive
% 2.60/0.97  --sup_prop_simpl_new                    true
% 2.60/0.97  --sup_prop_simpl_given                  true
% 2.60/0.97  --sup_fun_splitting                     false
% 2.60/0.97  --sup_smt_interval                      50000
% 2.60/0.97  
% 2.60/0.97  ------ Superposition Simplification Setup
% 2.60/0.97  
% 2.60/0.97  --sup_indices_passive                   []
% 2.60/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_full_bw                           [BwDemod]
% 2.60/0.97  --sup_immed_triv                        [TrivRules]
% 2.60/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_immed_bw_main                     []
% 2.60/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.97  
% 2.60/0.97  ------ Combination Options
% 2.60/0.97  
% 2.60/0.97  --comb_res_mult                         3
% 2.60/0.97  --comb_sup_mult                         2
% 2.60/0.97  --comb_inst_mult                        10
% 2.60/0.97  
% 2.60/0.97  ------ Debug Options
% 2.60/0.97  
% 2.60/0.97  --dbg_backtrace                         false
% 2.60/0.97  --dbg_dump_prop_clauses                 false
% 2.60/0.97  --dbg_dump_prop_clauses_file            -
% 2.60/0.97  --dbg_out_stat                          false
% 2.60/0.97  ------ Parsing...
% 2.60/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/0.97  
% 2.60/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.60/0.97  
% 2.60/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/0.97  
% 2.60/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/0.97  ------ Proving...
% 2.60/0.97  ------ Problem Properties 
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  clauses                                 21
% 2.60/0.97  conjectures                             2
% 2.60/0.97  EPR                                     11
% 2.60/0.97  Horn                                    19
% 2.60/0.97  unary                                   5
% 2.60/0.97  binary                                  7
% 2.60/0.97  lits                                    51
% 2.60/0.97  lits eq                                 11
% 2.60/0.97  fd_pure                                 0
% 2.60/0.97  fd_pseudo                               0
% 2.60/0.97  fd_cond                                 1
% 2.60/0.97  fd_pseudo_cond                          4
% 2.60/0.97  AC symbols                              0
% 2.60/0.97  
% 2.60/0.97  ------ Schedule dynamic 5 is on 
% 2.60/0.97  
% 2.60/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  ------ 
% 2.60/0.97  Current options:
% 2.60/0.97  ------ 
% 2.60/0.97  
% 2.60/0.97  ------ Input Options
% 2.60/0.97  
% 2.60/0.97  --out_options                           all
% 2.60/0.97  --tptp_safe_out                         true
% 2.60/0.97  --problem_path                          ""
% 2.60/0.97  --include_path                          ""
% 2.60/0.97  --clausifier                            res/vclausify_rel
% 2.60/0.97  --clausifier_options                    --mode clausify
% 2.60/0.97  --stdin                                 false
% 2.60/0.97  --stats_out                             all
% 2.60/0.97  
% 2.60/0.97  ------ General Options
% 2.60/0.97  
% 2.60/0.97  --fof                                   false
% 2.60/0.97  --time_out_real                         305.
% 2.60/0.97  --time_out_virtual                      -1.
% 2.60/0.97  --symbol_type_check                     false
% 2.60/0.97  --clausify_out                          false
% 2.60/0.97  --sig_cnt_out                           false
% 2.60/0.97  --trig_cnt_out                          false
% 2.60/0.97  --trig_cnt_out_tolerance                1.
% 2.60/0.97  --trig_cnt_out_sk_spl                   false
% 2.60/0.97  --abstr_cl_out                          false
% 2.60/0.97  
% 2.60/0.97  ------ Global Options
% 2.60/0.97  
% 2.60/0.97  --schedule                              default
% 2.60/0.97  --add_important_lit                     false
% 2.60/0.97  --prop_solver_per_cl                    1000
% 2.60/0.97  --min_unsat_core                        false
% 2.60/0.97  --soft_assumptions                      false
% 2.60/0.97  --soft_lemma_size                       3
% 2.60/0.97  --prop_impl_unit_size                   0
% 2.60/0.97  --prop_impl_unit                        []
% 2.60/0.97  --share_sel_clauses                     true
% 2.60/0.97  --reset_solvers                         false
% 2.60/0.97  --bc_imp_inh                            [conj_cone]
% 2.60/0.97  --conj_cone_tolerance                   3.
% 2.60/0.97  --extra_neg_conj                        none
% 2.60/0.97  --large_theory_mode                     true
% 2.60/0.97  --prolific_symb_bound                   200
% 2.60/0.97  --lt_threshold                          2000
% 2.60/0.97  --clause_weak_htbl                      true
% 2.60/0.97  --gc_record_bc_elim                     false
% 2.60/0.97  
% 2.60/0.97  ------ Preprocessing Options
% 2.60/0.97  
% 2.60/0.97  --preprocessing_flag                    true
% 2.60/0.97  --time_out_prep_mult                    0.1
% 2.60/0.97  --splitting_mode                        input
% 2.60/0.97  --splitting_grd                         true
% 2.60/0.97  --splitting_cvd                         false
% 2.60/0.97  --splitting_cvd_svl                     false
% 2.60/0.97  --splitting_nvd                         32
% 2.60/0.97  --sub_typing                            true
% 2.60/0.97  --prep_gs_sim                           true
% 2.60/0.97  --prep_unflatten                        true
% 2.60/0.97  --prep_res_sim                          true
% 2.60/0.97  --prep_upred                            true
% 2.60/0.97  --prep_sem_filter                       exhaustive
% 2.60/0.97  --prep_sem_filter_out                   false
% 2.60/0.97  --pred_elim                             true
% 2.60/0.97  --res_sim_input                         true
% 2.60/0.97  --eq_ax_congr_red                       true
% 2.60/0.97  --pure_diseq_elim                       true
% 2.60/0.97  --brand_transform                       false
% 2.60/0.97  --non_eq_to_eq                          false
% 2.60/0.97  --prep_def_merge                        true
% 2.60/0.97  --prep_def_merge_prop_impl              false
% 2.60/0.97  --prep_def_merge_mbd                    true
% 2.60/0.97  --prep_def_merge_tr_red                 false
% 2.60/0.97  --prep_def_merge_tr_cl                  false
% 2.60/0.97  --smt_preprocessing                     true
% 2.60/0.97  --smt_ac_axioms                         fast
% 2.60/0.97  --preprocessed_out                      false
% 2.60/0.97  --preprocessed_stats                    false
% 2.60/0.97  
% 2.60/0.97  ------ Abstraction refinement Options
% 2.60/0.97  
% 2.60/0.97  --abstr_ref                             []
% 2.60/0.97  --abstr_ref_prep                        false
% 2.60/0.97  --abstr_ref_until_sat                   false
% 2.60/0.97  --abstr_ref_sig_restrict                funpre
% 2.60/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.97  --abstr_ref_under                       []
% 2.60/0.97  
% 2.60/0.97  ------ SAT Options
% 2.60/0.97  
% 2.60/0.97  --sat_mode                              false
% 2.60/0.97  --sat_fm_restart_options                ""
% 2.60/0.97  --sat_gr_def                            false
% 2.60/0.97  --sat_epr_types                         true
% 2.60/0.97  --sat_non_cyclic_types                  false
% 2.60/0.97  --sat_finite_models                     false
% 2.60/0.97  --sat_fm_lemmas                         false
% 2.60/0.97  --sat_fm_prep                           false
% 2.60/0.97  --sat_fm_uc_incr                        true
% 2.60/0.97  --sat_out_model                         small
% 2.60/0.97  --sat_out_clauses                       false
% 2.60/0.97  
% 2.60/0.97  ------ QBF Options
% 2.60/0.97  
% 2.60/0.97  --qbf_mode                              false
% 2.60/0.97  --qbf_elim_univ                         false
% 2.60/0.97  --qbf_dom_inst                          none
% 2.60/0.97  --qbf_dom_pre_inst                      false
% 2.60/0.97  --qbf_sk_in                             false
% 2.60/0.97  --qbf_pred_elim                         true
% 2.60/0.97  --qbf_split                             512
% 2.60/0.97  
% 2.60/0.97  ------ BMC1 Options
% 2.60/0.97  
% 2.60/0.97  --bmc1_incremental                      false
% 2.60/0.97  --bmc1_axioms                           reachable_all
% 2.60/0.97  --bmc1_min_bound                        0
% 2.60/0.97  --bmc1_max_bound                        -1
% 2.60/0.97  --bmc1_max_bound_default                -1
% 2.60/0.97  --bmc1_symbol_reachability              true
% 2.60/0.97  --bmc1_property_lemmas                  false
% 2.60/0.97  --bmc1_k_induction                      false
% 2.60/0.97  --bmc1_non_equiv_states                 false
% 2.60/0.97  --bmc1_deadlock                         false
% 2.60/0.97  --bmc1_ucm                              false
% 2.60/0.97  --bmc1_add_unsat_core                   none
% 2.60/0.97  --bmc1_unsat_core_children              false
% 2.60/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.97  --bmc1_out_stat                         full
% 2.60/0.97  --bmc1_ground_init                      false
% 2.60/0.97  --bmc1_pre_inst_next_state              false
% 2.60/0.97  --bmc1_pre_inst_state                   false
% 2.60/0.97  --bmc1_pre_inst_reach_state             false
% 2.60/0.97  --bmc1_out_unsat_core                   false
% 2.60/0.97  --bmc1_aig_witness_out                  false
% 2.60/0.97  --bmc1_verbose                          false
% 2.60/0.97  --bmc1_dump_clauses_tptp                false
% 2.60/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.97  --bmc1_dump_file                        -
% 2.60/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.97  --bmc1_ucm_extend_mode                  1
% 2.60/0.97  --bmc1_ucm_init_mode                    2
% 2.60/0.97  --bmc1_ucm_cone_mode                    none
% 2.60/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.97  --bmc1_ucm_relax_model                  4
% 2.60/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.97  --bmc1_ucm_layered_model                none
% 2.60/0.97  --bmc1_ucm_max_lemma_size               10
% 2.60/0.97  
% 2.60/0.97  ------ AIG Options
% 2.60/0.97  
% 2.60/0.97  --aig_mode                              false
% 2.60/0.97  
% 2.60/0.97  ------ Instantiation Options
% 2.60/0.97  
% 2.60/0.97  --instantiation_flag                    true
% 2.60/0.97  --inst_sos_flag                         false
% 2.60/0.97  --inst_sos_phase                        true
% 2.60/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.97  --inst_lit_sel_side                     none
% 2.60/0.97  --inst_solver_per_active                1400
% 2.60/0.97  --inst_solver_calls_frac                1.
% 2.60/0.97  --inst_passive_queue_type               priority_queues
% 2.60/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.97  --inst_passive_queues_freq              [25;2]
% 2.60/0.97  --inst_dismatching                      true
% 2.60/0.97  --inst_eager_unprocessed_to_passive     true
% 2.60/0.97  --inst_prop_sim_given                   true
% 2.60/0.97  --inst_prop_sim_new                     false
% 2.60/0.97  --inst_subs_new                         false
% 2.60/0.97  --inst_eq_res_simp                      false
% 2.60/0.97  --inst_subs_given                       false
% 2.60/0.97  --inst_orphan_elimination               true
% 2.60/0.97  --inst_learning_loop_flag               true
% 2.60/0.97  --inst_learning_start                   3000
% 2.60/0.97  --inst_learning_factor                  2
% 2.60/0.97  --inst_start_prop_sim_after_learn       3
% 2.60/0.97  --inst_sel_renew                        solver
% 2.60/0.97  --inst_lit_activity_flag                true
% 2.60/0.97  --inst_restr_to_given                   false
% 2.60/0.97  --inst_activity_threshold               500
% 2.60/0.97  --inst_out_proof                        true
% 2.60/0.97  
% 2.60/0.97  ------ Resolution Options
% 2.60/0.97  
% 2.60/0.97  --resolution_flag                       false
% 2.60/0.97  --res_lit_sel                           adaptive
% 2.60/0.97  --res_lit_sel_side                      none
% 2.60/0.97  --res_ordering                          kbo
% 2.60/0.97  --res_to_prop_solver                    active
% 2.60/0.97  --res_prop_simpl_new                    false
% 2.60/0.97  --res_prop_simpl_given                  true
% 2.60/0.97  --res_passive_queue_type                priority_queues
% 2.60/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.97  --res_passive_queues_freq               [15;5]
% 2.60/0.97  --res_forward_subs                      full
% 2.60/0.97  --res_backward_subs                     full
% 2.60/0.97  --res_forward_subs_resolution           true
% 2.60/0.97  --res_backward_subs_resolution          true
% 2.60/0.97  --res_orphan_elimination                true
% 2.60/0.97  --res_time_limit                        2.
% 2.60/0.97  --res_out_proof                         true
% 2.60/0.97  
% 2.60/0.97  ------ Superposition Options
% 2.60/0.97  
% 2.60/0.97  --superposition_flag                    true
% 2.60/0.97  --sup_passive_queue_type                priority_queues
% 2.60/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.97  --demod_completeness_check              fast
% 2.60/0.97  --demod_use_ground                      true
% 2.60/0.97  --sup_to_prop_solver                    passive
% 2.60/0.97  --sup_prop_simpl_new                    true
% 2.60/0.97  --sup_prop_simpl_given                  true
% 2.60/0.97  --sup_fun_splitting                     false
% 2.60/0.97  --sup_smt_interval                      50000
% 2.60/0.97  
% 2.60/0.97  ------ Superposition Simplification Setup
% 2.60/0.97  
% 2.60/0.97  --sup_indices_passive                   []
% 2.60/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_full_bw                           [BwDemod]
% 2.60/0.97  --sup_immed_triv                        [TrivRules]
% 2.60/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_immed_bw_main                     []
% 2.60/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.97  
% 2.60/0.97  ------ Combination Options
% 2.60/0.97  
% 2.60/0.97  --comb_res_mult                         3
% 2.60/0.97  --comb_sup_mult                         2
% 2.60/0.97  --comb_inst_mult                        10
% 2.60/0.97  
% 2.60/0.97  ------ Debug Options
% 2.60/0.97  
% 2.60/0.97  --dbg_backtrace                         false
% 2.60/0.97  --dbg_dump_prop_clauses                 false
% 2.60/0.97  --dbg_dump_prop_clauses_file            -
% 2.60/0.97  --dbg_out_stat                          false
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  ------ Proving...
% 2.60/0.97  
% 2.60/0.97  
% 2.60/0.97  % SZS status Theorem for theBenchmark.p
% 2.60/0.97  
% 2.60/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/0.97  
% 2.60/0.97  fof(f5,axiom,(
% 2.60/0.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f54,plain,(
% 2.60/0.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f5])).
% 2.60/0.97  
% 2.60/0.97  fof(f6,axiom,(
% 2.60/0.97    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f55,plain,(
% 2.60/0.97    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f6])).
% 2.60/0.97  
% 2.60/0.97  fof(f2,axiom,(
% 2.60/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f17,plain,(
% 2.60/0.97    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.60/0.97    inference(ennf_transformation,[],[f2])).
% 2.60/0.97  
% 2.60/0.97  fof(f49,plain,(
% 2.60/0.97    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f17])).
% 2.60/0.97  
% 2.60/0.97  fof(f7,axiom,(
% 2.60/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f37,plain,(
% 2.60/0.97    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.60/0.97    inference(nnf_transformation,[],[f7])).
% 2.60/0.97  
% 2.60/0.97  fof(f56,plain,(
% 2.60/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f37])).
% 2.60/0.97  
% 2.60/0.97  fof(f1,axiom,(
% 2.60/0.97    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f33,plain,(
% 2.60/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.60/0.97    inference(nnf_transformation,[],[f1])).
% 2.60/0.97  
% 2.60/0.97  fof(f34,plain,(
% 2.60/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.60/0.97    inference(flattening,[],[f33])).
% 2.60/0.97  
% 2.60/0.97  fof(f48,plain,(
% 2.60/0.97    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f34])).
% 2.60/0.97  
% 2.60/0.97  fof(f4,axiom,(
% 2.60/0.97    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f18,plain,(
% 2.60/0.97    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 2.60/0.97    inference(ennf_transformation,[],[f4])).
% 2.60/0.97  
% 2.60/0.97  fof(f53,plain,(
% 2.60/0.97    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f18])).
% 2.60/0.97  
% 2.60/0.97  fof(f47,plain,(
% 2.60/0.97    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.60/0.97    inference(cnf_transformation,[],[f34])).
% 2.60/0.97  
% 2.60/0.97  fof(f75,plain,(
% 2.60/0.97    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.60/0.97    inference(equality_resolution,[],[f47])).
% 2.60/0.97  
% 2.60/0.97  fof(f14,conjecture,(
% 2.60/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.97  
% 2.60/0.97  fof(f15,negated_conjecture,(
% 2.60/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.60/0.98    inference(negated_conjecture,[],[f14])).
% 2.60/0.98  
% 2.60/0.98  fof(f31,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f15])).
% 2.60/0.98  
% 2.60/0.98  fof(f32,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f31])).
% 2.60/0.98  
% 2.60/0.98  fof(f39,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(nnf_transformation,[],[f32])).
% 2.60/0.98  
% 2.60/0.98  fof(f40,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f39])).
% 2.60/0.98  
% 2.60/0.98  fof(f44,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f43,plain,(
% 2.60/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f42,plain,(
% 2.60/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f41,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f45,plain,(
% 2.60/0.98    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43,f42,f41])).
% 2.60/0.98  
% 2.60/0.98  fof(f73,plain,(
% 2.60/0.98    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f46,plain,(
% 2.60/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f34])).
% 2.60/0.98  
% 2.60/0.98  fof(f3,axiom,(
% 2.60/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f35,plain,(
% 2.60/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/0.98    inference(nnf_transformation,[],[f3])).
% 2.60/0.98  
% 2.60/0.98  fof(f36,plain,(
% 2.60/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/0.98    inference(flattening,[],[f35])).
% 2.60/0.98  
% 2.60/0.98  fof(f52,plain,(
% 2.60/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f36])).
% 2.60/0.98  
% 2.60/0.98  fof(f71,plain,(
% 2.60/0.98    m2_orders_2(sK2,sK0,sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f72,plain,(
% 2.60/0.98    m2_orders_2(sK3,sK0,sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f13,axiom,(
% 2.60/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f29,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f13])).
% 2.60/0.98  
% 2.60/0.98  fof(f30,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f29])).
% 2.60/0.98  
% 2.60/0.98  fof(f38,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(nnf_transformation,[],[f30])).
% 2.60/0.98  
% 2.60/0.98  fof(f64,plain,(
% 2.60/0.98    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f38])).
% 2.60/0.98  
% 2.60/0.98  fof(f70,plain,(
% 2.60/0.98    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f69,plain,(
% 2.60/0.98    l1_orders_2(sK0)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f65,plain,(
% 2.60/0.98    ~v2_struct_0(sK0)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f66,plain,(
% 2.60/0.98    v3_orders_2(sK0)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f67,plain,(
% 2.60/0.98    v4_orders_2(sK0)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f68,plain,(
% 2.60/0.98    v5_orders_2(sK0)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f9,axiom,(
% 2.60/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f16,plain,(
% 2.60/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.60/0.98    inference(pure_predicate_removal,[],[f9])).
% 2.60/0.98  
% 2.60/0.98  fof(f21,plain,(
% 2.60/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f16])).
% 2.60/0.98  
% 2.60/0.98  fof(f22,plain,(
% 2.60/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f21])).
% 2.60/0.98  
% 2.60/0.98  fof(f59,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f22])).
% 2.60/0.98  
% 2.60/0.98  fof(f10,axiom,(
% 2.60/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f23,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f10])).
% 2.60/0.98  
% 2.60/0.98  fof(f24,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f23])).
% 2.60/0.98  
% 2.60/0.98  fof(f60,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f24])).
% 2.60/0.98  
% 2.60/0.98  fof(f11,axiom,(
% 2.60/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f25,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f11])).
% 2.60/0.98  
% 2.60/0.98  fof(f26,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f25])).
% 2.60/0.98  
% 2.60/0.98  fof(f61,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f26])).
% 2.60/0.98  
% 2.60/0.98  fof(f8,axiom,(
% 2.60/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f19,plain,(
% 2.60/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f8])).
% 2.60/0.98  
% 2.60/0.98  fof(f20,plain,(
% 2.60/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f19])).
% 2.60/0.98  
% 2.60/0.98  fof(f58,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f20])).
% 2.60/0.98  
% 2.60/0.98  fof(f74,plain,(
% 2.60/0.98    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.60/0.98    inference(cnf_transformation,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f12,axiom,(
% 2.60/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f27,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f12])).
% 2.60/0.98  
% 2.60/0.98  fof(f28,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f27])).
% 2.60/0.98  
% 2.60/0.98  fof(f62,plain,(
% 2.60/0.98    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f28])).
% 2.60/0.98  
% 2.60/0.98  cnf(c_8,plain,
% 2.60/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1535,plain,
% 2.60/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_9,plain,
% 2.60/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1534,plain,
% 2.60/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3,plain,
% 2.60/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1538,plain,
% 2.60/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 2.60/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2758,plain,
% 2.60/0.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1534,c_1538]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_11,plain,
% 2.60/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.60/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1532,plain,
% 2.60/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2869,plain,
% 2.60/0.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2758,c_1532]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_0,plain,
% 2.60/0.98      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.60/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_7,plain,
% 2.60/0.98      ( ~ r2_xboole_0(X0,X1) | k4_xboole_0(X1,X0) != k1_xboole_0 ),
% 2.60/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_374,plain,
% 2.60/0.98      ( ~ r1_tarski(X0,X1)
% 2.60/0.98      | X1 = X0
% 2.60/0.98      | k4_xboole_0(X1,X0) != k1_xboole_0 ),
% 2.60/0.98      inference(resolution,[status(thm)],[c_0,c_7]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1529,plain,
% 2.60/0.98      ( X0 = X1
% 2.60/0.98      | k4_xboole_0(X0,X1) != k1_xboole_0
% 2.60/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3595,plain,
% 2.60/0.98      ( k4_xboole_0(X0,X1) = X1
% 2.60/0.98      | k1_xboole_0 != X1
% 2.60/0.98      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2869,c_1529]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5153,plain,
% 2.60/0.98      ( k4_xboole_0(X0,k1_xboole_0) = k1_xboole_0
% 2.60/0.98      | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.60/0.98      inference(equality_resolution,[status(thm)],[c_3595]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5285,plain,
% 2.60/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1535,c_5153]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5524,plain,
% 2.60/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_5285,c_1534]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1,plain,
% 2.60/0.98      ( ~ r2_xboole_0(X0,X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_20,negated_conjecture,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.60/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_218,plain,
% 2.60/0.98      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.60/0.98      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_219,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_218]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_423,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_219]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_424,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_423]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1525,plain,
% 2.60/0.98      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2,plain,
% 2.60/0.98      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_413,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3)
% 2.60/0.98      | r1_tarski(X0,X1)
% 2.60/0.98      | sK3 != X1
% 2.60/0.98      | sK2 != X0 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_219]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_414,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_413]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_415,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.60/0.98      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_425,plain,
% 2.60/0.98      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4,plain,
% 2.60/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.60/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2048,plain,
% 2.60/0.98      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2659,plain,
% 2.60/0.98      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_2048]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2660,plain,
% 2.60/0.98      ( sK2 = sK3
% 2.60/0.98      | r1_tarski(sK3,sK2) != iProver_top
% 2.60/0.98      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2659]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_22,negated_conjecture,
% 2.60/0.98      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1530,plain,
% 2.60/0.98      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_21,negated_conjecture,
% 2.60/0.98      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1531,plain,
% 2.60/0.98      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_17,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m2_orders_2(X3,X1,X2)
% 2.60/0.98      | m1_orders_2(X3,X1,X0)
% 2.60/0.98      | m1_orders_2(X0,X1,X3)
% 2.60/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | X3 = X0 ),
% 2.60/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_23,negated_conjecture,
% 2.60/0.98      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.60/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_489,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m2_orders_2(X3,X1,X2)
% 2.60/0.98      | m1_orders_2(X3,X1,X0)
% 2.60/0.98      | m1_orders_2(X0,X1,X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | X3 = X0
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK1 != X2 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_490,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | ~ m2_orders_2(X2,X1,sK1)
% 2.60/0.98      | m1_orders_2(X0,X1,X2)
% 2.60/0.98      | m1_orders_2(X2,X1,X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | X0 = X2
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_489]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_24,negated_conjecture,
% 2.60/0.98      ( l1_orders_2(sK0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_657,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | ~ m2_orders_2(X2,X1,sK1)
% 2.60/0.98      | m1_orders_2(X0,X1,X2)
% 2.60/0.98      | m1_orders_2(X2,X1,X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | X2 = X0
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK0 != X1 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_490,c_24]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_658,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | v2_struct_0(sK0)
% 2.60/0.98      | ~ v3_orders_2(sK0)
% 2.60/0.98      | ~ v4_orders_2(sK0)
% 2.60/0.98      | ~ v5_orders_2(sK0)
% 2.60/0.98      | X1 = X0
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_657]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_28,negated_conjecture,
% 2.60/0.98      ( ~ v2_struct_0(sK0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_27,negated_conjecture,
% 2.60/0.98      ( v3_orders_2(sK0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_26,negated_conjecture,
% 2.60/0.98      ( v4_orders_2(sK0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_25,negated_conjecture,
% 2.60/0.98      ( v5_orders_2(sK0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_662,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | X1 = X0
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_658,c_28,c_27,c_26,c_25]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_839,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | X1 = X0 ),
% 2.60/0.98      inference(equality_resolution_simp,[status(thm)],[c_662]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1520,plain,
% 2.60/0.98      ( X0 = X1
% 2.60/0.98      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.60/0.98      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.60/0.98      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2610,plain,
% 2.60/0.98      ( sK3 = X0
% 2.60/0.98      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.60/0.98      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1531,c_1520]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3120,plain,
% 2.60/0.98      ( sK3 = sK2
% 2.60/0.98      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.60/0.98      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1530,c_2610]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_35,plain,
% 2.60/0.98      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_36,plain,
% 2.60/0.98      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2049,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.60/0.98      | m1_orders_2(X0,sK0,sK3)
% 2.60/0.98      | m1_orders_2(sK3,sK0,X0)
% 2.60/0.98      | X0 = sK3 ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_839]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2747,plain,
% 2.60/0.98      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.60/0.98      | m1_orders_2(sK3,sK0,sK2)
% 2.60/0.98      | m1_orders_2(sK2,sK0,sK3)
% 2.60/0.98      | sK2 = sK3 ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_2049]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2748,plain,
% 2.60/0.98      ( sK2 = sK3
% 2.60/0.98      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.60/0.98      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.60/0.98      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2747]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3129,plain,
% 2.60/0.98      ( m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.60/0.98      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_3120,c_35,c_36,c_425,c_2748]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_13,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_561,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK1 != X2 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_562,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_561]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_612,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK0 != X1 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_562,c_24]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_613,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | v2_struct_0(sK0)
% 2.60/0.98      | ~ v3_orders_2(sK0)
% 2.60/0.98      | ~ v4_orders_2(sK0)
% 2.60/0.98      | ~ v5_orders_2(sK0)
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_612]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_617,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_613,c_28,c_27,c_26,c_25]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_847,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.60/0.98      inference(equality_resolution_simp,[status(thm)],[c_617]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1518,plain,
% 2.60/0.98      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_14,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | r1_tarski(X0,X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_741,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | r1_tarski(X0,X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | sK0 != X1 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_742,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | r1_tarski(X0,X1)
% 2.60/0.98      | v2_struct_0(sK0)
% 2.60/0.98      | ~ v3_orders_2(sK0)
% 2.60/0.98      | ~ v4_orders_2(sK0)
% 2.60/0.98      | ~ v5_orders_2(sK0) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_741]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_744,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | r1_tarski(X0,X1) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_742,c_28,c_27,c_26,c_25]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1523,plain,
% 2.60/0.98      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.60/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.60/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1785,plain,
% 2.60/0.98      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.60/0.98      | r1_tarski(X1,X0) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1518,c_1523]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1906,plain,
% 2.60/0.98      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.60/0.98      | r1_tarski(X0,sK2) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1530,c_1785]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3135,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.60/0.98      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_3129,c_1906]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4049,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_1525,c_415,c_425,c_2660,c_3135]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_15,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_orders_2(X2,X1,X0)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_xboole_0 = X2 ),
% 2.60/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_12,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_158,plain,
% 2.60/0.98      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ m1_orders_2(X2,X1,X0)
% 2.60/0.98      | ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_xboole_0 = X2 ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_15,c_12]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_159,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_orders_2(X2,X1,X0)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_xboole_0 = X2 ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_158]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_717,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_orders_2(X2,X1,X0)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | sK0 != X1
% 2.60/0.98      | k1_xboole_0 = X2 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_159,c_24]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_718,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | ~ m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | v2_struct_0(sK0)
% 2.60/0.98      | ~ v3_orders_2(sK0)
% 2.60/0.98      | ~ v4_orders_2(sK0)
% 2.60/0.98      | ~ v5_orders_2(sK0)
% 2.60/0.98      | k1_xboole_0 = X0 ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_717]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_722,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | ~ m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | k1_xboole_0 = X0 ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_718,c_28,c_27,c_26,c_25]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_723,plain,
% 2.60/0.98      ( ~ m1_orders_2(X0,sK0,X1)
% 2.60/0.98      | ~ m1_orders_2(X1,sK0,X0)
% 2.60/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | k1_xboole_0 = X1 ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_722]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1524,plain,
% 2.60/0.98      ( k1_xboole_0 = X0
% 2.60/0.98      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.60/0.98      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1783,plain,
% 2.60/0.98      ( k1_xboole_0 = X0
% 2.60/0.98      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.60/0.98      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1518,c_1524]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3847,plain,
% 2.60/0.98      ( sK3 = k1_xboole_0
% 2.60/0.98      | m1_orders_2(X0,sK0,sK3) != iProver_top
% 2.60/0.98      | m1_orders_2(sK3,sK0,X0) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1531,c_1783]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4060,plain,
% 2.60/0.98      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK0,sK2) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_4049,c_3847]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1905,plain,
% 2.60/0.98      ( m1_orders_2(X0,sK0,sK3) != iProver_top
% 2.60/0.98      | r1_tarski(X0,sK3) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1531,c_1785]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4062,plain,
% 2.60/0.98      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_4049,c_1905]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1537,plain,
% 2.60/0.98      ( X0 = X1
% 2.60/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.60/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4132,plain,
% 2.60/0.98      ( sK3 = sK2 | r1_tarski(sK3,sK2) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_4062,c_1537]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_19,negated_conjecture,
% 2.60/0.98      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.60/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_216,plain,
% 2.60/0.98      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.60/0.98      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_217,plain,
% 2.60/0.98      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_216]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_390,plain,
% 2.60/0.98      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.60/0.98      | ~ r1_tarski(X0,X1)
% 2.60/0.98      | X1 = X0
% 2.60/0.98      | sK3 != X1
% 2.60/0.98      | sK2 != X0 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_217]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_391,plain,
% 2.60/0.98      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_390]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_392,plain,
% 2.60/0.98      ( sK3 = sK2
% 2.60/0.98      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.60/0.98      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1688,plain,
% 2.60/0.98      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.60/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_847]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1689,plain,
% 2.60/0.98      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.60/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_1688]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1704,plain,
% 2.60/0.98      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.60/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.60/0.98      | r1_tarski(sK2,sK3) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_744]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1705,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.60/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.60/0.98      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_1704]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4135,plain,
% 2.60/0.98      ( sK3 = sK2 ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_4132,c_36,c_392,c_415,c_425,c_1689,c_1705,c_2660,
% 2.60/0.98                 c_3135]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4248,plain,
% 2.60/0.98      ( sK3 = k1_xboole_0 | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
% 2.60/0.98      inference(light_normalisation,[status(thm)],[c_4060,c_4135]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4249,plain,
% 2.60/0.98      ( sK2 = k1_xboole_0 | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
% 2.60/0.98      inference(demodulation,[status(thm)],[c_4248,c_4135]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4145,plain,
% 2.60/0.98      ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 2.60/0.98      inference(demodulation,[status(thm)],[c_4135,c_3129]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4253,plain,
% 2.60/0.98      ( sK2 = k1_xboole_0 ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_4249,c_4145]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_16,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m2_orders_2(X3,X1,X2)
% 2.60/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ r1_xboole_0(X0,X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_528,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 2.60/0.98      | ~ m2_orders_2(X3,X1,X2)
% 2.60/0.98      | ~ r1_xboole_0(X0,X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK1 != X2 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_529,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | ~ m2_orders_2(X2,X1,sK1)
% 2.60/0.98      | ~ r1_xboole_0(X2,X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | ~ l1_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_528]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_633,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,X1,sK1)
% 2.60/0.98      | ~ m2_orders_2(X2,X1,sK1)
% 2.60/0.98      | ~ r1_xboole_0(X2,X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ v3_orders_2(X1)
% 2.60/0.98      | ~ v4_orders_2(X1)
% 2.60/0.98      | ~ v5_orders_2(X1)
% 2.60/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.60/0.98      | sK0 != X1 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_529,c_24]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_634,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | ~ r1_xboole_0(X1,X0)
% 2.60/0.98      | v2_struct_0(sK0)
% 2.60/0.98      | ~ v3_orders_2(sK0)
% 2.60/0.98      | ~ v4_orders_2(sK0)
% 2.60/0.98      | ~ v5_orders_2(sK0)
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_633]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_638,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | ~ r1_xboole_0(X1,X0)
% 2.60/0.98      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_634,c_28,c_27,c_26,c_25]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_843,plain,
% 2.60/0.98      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.60/0.98      | ~ m2_orders_2(X1,sK0,sK1)
% 2.60/0.98      | ~ r1_xboole_0(X1,X0) ),
% 2.60/0.98      inference(equality_resolution_simp,[status(thm)],[c_638]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1519,plain,
% 2.60/0.98      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.60/0.98      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_1986,plain,
% 2.60/0.98      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.60/0.98      | r1_xboole_0(X0,sK2) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1530,c_1519]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2347,plain,
% 2.60/0.98      ( r1_xboole_0(sK2,sK2) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_1530,c_1986]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4262,plain,
% 2.60/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.60/0.98      inference(demodulation,[status(thm)],[c_4253,c_2347]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(contradiction,plain,
% 2.60/0.98      ( $false ),
% 2.60/0.98      inference(minisat,[status(thm)],[c_5524,c_4262]) ).
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/0.98  
% 2.60/0.98  ------                               Statistics
% 2.60/0.98  
% 2.60/0.98  ------ General
% 2.60/0.98  
% 2.60/0.98  abstr_ref_over_cycles:                  0
% 2.60/0.98  abstr_ref_under_cycles:                 0
% 2.60/0.98  gc_basic_clause_elim:                   0
% 2.60/0.98  forced_gc_time:                         0
% 2.60/0.98  parsing_time:                           0.011
% 2.60/0.98  unif_index_cands_time:                  0.
% 2.60/0.98  unif_index_add_time:                    0.
% 2.60/0.98  orderings_time:                         0.
% 2.60/0.98  out_proof_time:                         0.01
% 2.60/0.98  total_time:                             0.178
% 2.60/0.98  num_of_symbols:                         52
% 2.60/0.98  num_of_terms:                           3871
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing
% 2.60/0.98  
% 2.60/0.98  num_of_splits:                          0
% 2.60/0.98  num_of_split_atoms:                     0
% 2.60/0.98  num_of_reused_defs:                     0
% 2.60/0.98  num_eq_ax_congr_red:                    9
% 2.60/0.98  num_of_sem_filtered_clauses:            1
% 2.60/0.98  num_of_subtypes:                        0
% 2.60/0.98  monotx_restored_types:                  0
% 2.60/0.98  sat_num_of_epr_types:                   0
% 2.60/0.98  sat_num_of_non_cyclic_types:            0
% 2.60/0.98  sat_guarded_non_collapsed_types:        0
% 2.60/0.98  num_pure_diseq_elim:                    0
% 2.60/0.98  simp_replaced_by:                       0
% 2.60/0.98  res_preprocessed:                       112
% 2.60/0.98  prep_upred:                             0
% 2.60/0.98  prep_unflattend:                        20
% 2.60/0.98  smt_new_axioms:                         0
% 2.60/0.98  pred_elim_cands:                        5
% 2.60/0.98  pred_elim:                              7
% 2.60/0.98  pred_elim_cl:                           7
% 2.60/0.98  pred_elim_cycles:                       9
% 2.60/0.98  merged_defs:                            10
% 2.60/0.98  merged_defs_ncl:                        0
% 2.60/0.98  bin_hyper_res:                          10
% 2.60/0.98  prep_cycles:                            4
% 2.60/0.98  pred_elim_time:                         0.01
% 2.60/0.98  splitting_time:                         0.
% 2.60/0.98  sem_filter_time:                        0.
% 2.60/0.98  monotx_time:                            0.
% 2.60/0.98  subtype_inf_time:                       0.
% 2.60/0.98  
% 2.60/0.98  ------ Problem properties
% 2.60/0.98  
% 2.60/0.98  clauses:                                21
% 2.60/0.98  conjectures:                            2
% 2.60/0.98  epr:                                    11
% 2.60/0.98  horn:                                   19
% 2.60/0.98  ground:                                 6
% 2.60/0.98  unary:                                  5
% 2.60/0.98  binary:                                 7
% 2.60/0.98  lits:                                   51
% 2.60/0.98  lits_eq:                                11
% 2.60/0.98  fd_pure:                                0
% 2.60/0.98  fd_pseudo:                              0
% 2.60/0.98  fd_cond:                                1
% 2.60/0.98  fd_pseudo_cond:                         4
% 2.60/0.98  ac_symbols:                             0
% 2.60/0.98  
% 2.60/0.98  ------ Propositional Solver
% 2.60/0.98  
% 2.60/0.98  prop_solver_calls:                      27
% 2.60/0.98  prop_fast_solver_calls:                 953
% 2.60/0.98  smt_solver_calls:                       0
% 2.60/0.98  smt_fast_solver_calls:                  0
% 2.60/0.98  prop_num_of_clauses:                    1815
% 2.60/0.98  prop_preprocess_simplified:             5235
% 2.60/0.98  prop_fo_subsumed:                       37
% 2.60/0.98  prop_solver_time:                       0.
% 2.60/0.98  smt_solver_time:                        0.
% 2.60/0.98  smt_fast_solver_time:                   0.
% 2.60/0.98  prop_fast_solver_time:                  0.
% 2.60/0.98  prop_unsat_core_time:                   0.
% 2.60/0.98  
% 2.60/0.98  ------ QBF
% 2.60/0.98  
% 2.60/0.98  qbf_q_res:                              0
% 2.60/0.98  qbf_num_tautologies:                    0
% 2.60/0.98  qbf_prep_cycles:                        0
% 2.60/0.98  
% 2.60/0.98  ------ BMC1
% 2.60/0.98  
% 2.60/0.98  bmc1_current_bound:                     -1
% 2.60/0.98  bmc1_last_solved_bound:                 -1
% 2.60/0.98  bmc1_unsat_core_size:                   -1
% 2.60/0.98  bmc1_unsat_core_parents_size:           -1
% 2.60/0.98  bmc1_merge_next_fun:                    0
% 2.60/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.60/0.98  
% 2.60/0.98  ------ Instantiation
% 2.60/0.98  
% 2.60/0.98  inst_num_of_clauses:                    499
% 2.60/0.98  inst_num_in_passive:                    142
% 2.60/0.98  inst_num_in_active:                     320
% 2.60/0.98  inst_num_in_unprocessed:                37
% 2.60/0.98  inst_num_of_loops:                      340
% 2.60/0.98  inst_num_of_learning_restarts:          0
% 2.60/0.98  inst_num_moves_active_passive:          15
% 2.60/0.98  inst_lit_activity:                      0
% 2.60/0.98  inst_lit_activity_moves:                0
% 2.60/0.98  inst_num_tautologies:                   0
% 2.60/0.98  inst_num_prop_implied:                  0
% 2.60/0.98  inst_num_existing_simplified:           0
% 2.60/0.98  inst_num_eq_res_simplified:             0
% 2.60/0.98  inst_num_child_elim:                    0
% 2.60/0.98  inst_num_of_dismatching_blockings:      263
% 2.60/0.98  inst_num_of_non_proper_insts:           626
% 2.60/0.98  inst_num_of_duplicates:                 0
% 2.60/0.98  inst_inst_num_from_inst_to_res:         0
% 2.60/0.98  inst_dismatching_checking_time:         0.
% 2.60/0.98  
% 2.60/0.98  ------ Resolution
% 2.60/0.98  
% 2.60/0.98  res_num_of_clauses:                     0
% 2.60/0.98  res_num_in_passive:                     0
% 2.60/0.98  res_num_in_active:                      0
% 2.60/0.98  res_num_of_loops:                       116
% 2.60/0.98  res_forward_subset_subsumed:            60
% 2.60/0.98  res_backward_subset_subsumed:           2
% 2.60/0.98  res_forward_subsumed:                   0
% 2.60/0.98  res_backward_subsumed:                  0
% 2.60/0.98  res_forward_subsumption_resolution:     0
% 2.60/0.98  res_backward_subsumption_resolution:    0
% 2.60/0.98  res_clause_to_clause_subsumption:       208
% 2.60/0.98  res_orphan_elimination:                 0
% 2.60/0.98  res_tautology_del:                      98
% 2.60/0.98  res_num_eq_res_simplified:              4
% 2.60/0.98  res_num_sel_changes:                    0
% 2.60/0.98  res_moves_from_active_to_pass:          0
% 2.60/0.98  
% 2.60/0.98  ------ Superposition
% 2.60/0.98  
% 2.60/0.98  sup_time_total:                         0.
% 2.60/0.98  sup_time_generating:                    0.
% 2.60/0.98  sup_time_sim_full:                      0.
% 2.60/0.98  sup_time_sim_immed:                     0.
% 2.60/0.98  
% 2.60/0.98  sup_num_of_clauses:                     43
% 2.60/0.98  sup_num_in_active:                      40
% 2.60/0.98  sup_num_in_passive:                     3
% 2.60/0.98  sup_num_of_loops:                       67
% 2.60/0.98  sup_fw_superposition:                   48
% 2.60/0.98  sup_bw_superposition:                   53
% 2.60/0.98  sup_immediate_simplified:               17
% 2.60/0.98  sup_given_eliminated:                   0
% 2.60/0.98  comparisons_done:                       0
% 2.60/0.98  comparisons_avoided:                    0
% 2.60/0.98  
% 2.60/0.98  ------ Simplifications
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  sim_fw_subset_subsumed:                 10
% 2.60/0.98  sim_bw_subset_subsumed:                 11
% 2.60/0.98  sim_fw_subsumed:                        5
% 2.60/0.98  sim_bw_subsumed:                        0
% 2.60/0.98  sim_fw_subsumption_res:                 1
% 2.60/0.98  sim_bw_subsumption_res:                 0
% 2.60/0.98  sim_tautology_del:                      1
% 2.60/0.98  sim_eq_tautology_del:                   7
% 2.60/0.98  sim_eq_res_simp:                        0
% 2.60/0.98  sim_fw_demodulated:                     3
% 2.60/0.98  sim_bw_demodulated:                     27
% 2.60/0.98  sim_light_normalised:                   5
% 2.60/0.98  sim_joinable_taut:                      0
% 2.60/0.98  sim_joinable_simp:                      0
% 2.60/0.98  sim_ac_normalised:                      0
% 2.60/0.98  sim_smt_subsumption:                    0
% 2.60/0.98  
%------------------------------------------------------------------------------
