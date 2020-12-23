%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:48 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  204 (4371 expanded)
%              Number of clauses        :  134 ( 810 expanded)
%              Number of leaves         :   19 (1429 expanded)
%              Depth                    :   30
%              Number of atoms          :  962 (42009 expanded)
%              Number of equality atoms :  242 (1056 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f38])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f43,f42,f41,f40])).

fof(f69,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
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

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f71,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_362,plain,
    ( r1_tarski(X0,X1)
    | X2 != X1
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_363,plain,
    ( r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1478,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1482,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1479,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_469,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_470,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_809,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_23])).

cnf(c_810,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_814,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_810,c_27,c_26,c_25,c_24])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_851,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_852,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_856,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_27,c_26,c_25,c_24])).

cnf(c_922,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1))
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_814,c_856])).

cnf(c_995,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_922])).

cnf(c_1471,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X0,sK1,X0) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_2568,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1471])).

cnf(c_34,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1119,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1672,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_2111,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_1118,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2112,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_2154,plain,
    ( ~ m1_orders_2(sK3,sK1,sK3)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_2159,plain,
    ( k1_xboole_0 = sK3
    | m1_orders_2(sK3,sK1,sK3) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1480,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_538,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_539,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_749,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_539,c_23])).

cnf(c_750,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_754,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_27,c_26,c_25,c_24])).

cnf(c_1007,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_754])).

cnf(c_1468,plain,
    ( X0 = X1
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_1989,plain,
    ( sK4 = X0
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1468])).

cnf(c_2351,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1989])).

cnf(c_35,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_200,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_201,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_399,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_201])).

cnf(c_400,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_401,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1771,plain,
    ( m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1775,plain,
    ( sK3 = sK4
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1771])).

cnf(c_2360,plain,
    ( m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_34,c_35,c_401,c_1775])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_872,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_873,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_875,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_27,c_26,c_25,c_24])).

cnf(c_949,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m2_orders_2(X2,sK1,sK2)
    | r1_tarski(X0,X1)
    | X1 != X2
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_814,c_875])).

cnf(c_950,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m2_orders_2(X1,sK1,sK2)
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_1472,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_1710,plain,
    ( m1_orders_2(X0,sK1,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1472])).

cnf(c_2366,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_1710])).

cnf(c_387,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_201])).

cnf(c_388,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_389,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1777,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1778,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_2445,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2366,c_389,c_401,c_1778])).

cnf(c_17,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_499,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_500,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_779,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_500,c_23])).

cnf(c_780,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_784,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_27,c_26,c_25,c_24])).

cnf(c_1003,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_784])).

cnf(c_1469,plain,
    ( X0 = X1
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_1835,plain,
    ( sK4 = X0
    | m1_orders_2(X0,sK1,sK4) != iProver_top
    | m1_orders_2(sK4,sK1,X0) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1469])).

cnf(c_2214,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1835])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_198,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_199,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_374,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_199])).

cnf(c_375,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_376,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1629,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1630,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_2282,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_35,c_376,c_1630])).

cnf(c_2450,plain,
    ( sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_2445,c_2282])).

cnf(c_2456,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2450,c_2445])).

cnf(c_2727,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2568,c_34,c_2111,c_2112,c_2159,c_2456])).

cnf(c_2734,plain,
    ( m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2727,c_1479])).

cnf(c_15,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_439,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_440,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_830,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_440,c_23])).

cnf(c_831,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_835,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_27,c_26,c_25,c_24])).

cnf(c_999,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_835])).

cnf(c_1470,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1484,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2632,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1484])).

cnf(c_3361,plain,
    ( r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_2632])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1481,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3369,plain,
    ( r1_tarski(X0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_1481])).

cnf(c_3469,plain,
    ( r1_tarski(k1_xboole_0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_3369])).

cnf(c_3633,plain,
    ( k1_funct_1(sK2,u1_struct_0(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1478,c_3469])).

cnf(c_2090,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_tarski(X0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1481])).

cnf(c_3237,plain,
    ( m2_orders_2(k1_funct_1(sK2,u1_struct_0(sK1)),sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_2090])).

cnf(c_3764,plain,
    ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3633,c_3237])).

cnf(c_1123,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1642,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X2 != sK2
    | X0 != sK4
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1756,plain,
    ( m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X0 != sK4
    | X1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2257,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m2_orders_2(k1_xboole_0,X0,sK2)
    | X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_2259,plain,
    ( X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2257])).

cnf(c_2261,plain,
    ( sK2 != sK2
    | sK1 != sK1
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_1780,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_2126,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_1757,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_409,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_199])).

cnf(c_410,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_70,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_66,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3764,c_2456,c_2445,c_2282,c_2261,c_2159,c_2126,c_2112,c_2111,c_1757,c_410,c_400,c_70,c_66,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/0.99  
% 1.87/0.99  ------  iProver source info
% 1.87/0.99  
% 1.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/0.99  git: non_committed_changes: false
% 1.87/0.99  git: last_make_outside_of_git: false
% 1.87/0.99  
% 1.87/0.99  ------ 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options
% 1.87/0.99  
% 1.87/0.99  --out_options                           all
% 1.87/0.99  --tptp_safe_out                         true
% 1.87/0.99  --problem_path                          ""
% 1.87/0.99  --include_path                          ""
% 1.87/0.99  --clausifier                            res/vclausify_rel
% 1.87/0.99  --clausifier_options                    --mode clausify
% 1.87/0.99  --stdin                                 false
% 1.87/0.99  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     num_symb
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       true
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  ------ Parsing...
% 1.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/0.99  ------ Proving...
% 1.87/0.99  ------ Problem Properties 
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  clauses                                 19
% 1.87/0.99  conjectures                             2
% 1.87/0.99  EPR                                     16
% 1.87/0.99  Horn                                    15
% 1.87/0.99  unary                                   3
% 1.87/0.99  binary                                  8
% 1.87/0.99  lits                                    47
% 1.87/0.99  lits eq                                 9
% 1.87/0.99  fd_pure                                 0
% 1.87/0.99  fd_pseudo                               0
% 1.87/0.99  fd_cond                                 2
% 1.87/0.99  fd_pseudo_cond                          3
% 1.87/0.99  AC symbols                              0
% 1.87/0.99  
% 1.87/0.99  ------ Schedule dynamic 5 is on 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ 
% 1.87/0.99  Current options:
% 1.87/0.99  ------ 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options
% 1.87/0.99  
% 1.87/0.99  --out_options                           all
% 1.87/0.99  --tptp_safe_out                         true
% 1.87/0.99  --problem_path                          ""
% 1.87/0.99  --include_path                          ""
% 1.87/0.99  --clausifier                            res/vclausify_rel
% 1.87/0.99  --clausifier_options                    --mode clausify
% 1.87/0.99  --stdin                                 false
% 1.87/0.99  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     none
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       false
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ Proving...
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS status Theorem for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  fof(f2,axiom,(
% 1.87/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f33,plain,(
% 1.87/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.87/0.99    inference(nnf_transformation,[],[f2])).
% 1.87/0.99  
% 1.87/0.99  fof(f34,plain,(
% 1.87/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.87/0.99    inference(flattening,[],[f33])).
% 1.87/0.99  
% 1.87/0.99  fof(f48,plain,(
% 1.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f34])).
% 1.87/0.99  
% 1.87/0.99  fof(f4,axiom,(
% 1.87/0.99    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f15,plain,(
% 1.87/0.99    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.87/0.99    inference(ennf_transformation,[],[f4])).
% 1.87/0.99  
% 1.87/0.99  fof(f54,plain,(
% 1.87/0.99    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.87/0.99    inference(cnf_transformation,[],[f15])).
% 1.87/0.99  
% 1.87/0.99  fof(f3,axiom,(
% 1.87/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f35,plain,(
% 1.87/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.99    inference(nnf_transformation,[],[f3])).
% 1.87/0.99  
% 1.87/0.99  fof(f36,plain,(
% 1.87/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.99    inference(flattening,[],[f35])).
% 1.87/0.99  
% 1.87/0.99  fof(f51,plain,(
% 1.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.87/0.99    inference(cnf_transformation,[],[f36])).
% 1.87/0.99  
% 1.87/0.99  fof(f75,plain,(
% 1.87/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.87/0.99    inference(equality_resolution,[],[f51])).
% 1.87/0.99  
% 1.87/0.99  fof(f11,conjecture,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f12,negated_conjecture,(
% 1.87/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.87/0.99    inference(negated_conjecture,[],[f11])).
% 1.87/0.99  
% 1.87/0.99  fof(f27,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f12])).
% 1.87/0.99  
% 1.87/0.99  fof(f28,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f27])).
% 1.87/0.99  
% 1.87/0.99  fof(f38,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.87/0.99    inference(nnf_transformation,[],[f28])).
% 1.87/0.99  
% 1.87/0.99  fof(f39,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f38])).
% 1.87/0.99  
% 1.87/0.99  fof(f43,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f42,plain,(
% 1.87/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f41,plain,(
% 1.87/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f40,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f44,plain,(
% 1.87/0.99    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f43,f42,f41,f40])).
% 1.87/0.99  
% 1.87/0.99  fof(f69,plain,(
% 1.87/0.99    m2_orders_2(sK3,sK1,sK2)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f6,axiom,(
% 1.87/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f13,plain,(
% 1.87/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.87/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.87/0.99  
% 1.87/0.99  fof(f17,plain,(
% 1.87/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f13])).
% 1.87/0.99  
% 1.87/0.99  fof(f18,plain,(
% 1.87/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f17])).
% 1.87/0.99  
% 1.87/0.99  fof(f56,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f68,plain,(
% 1.87/0.99    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f67,plain,(
% 1.87/0.99    l1_orders_2(sK1)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f63,plain,(
% 1.87/0.99    ~v2_struct_0(sK1)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f64,plain,(
% 1.87/0.99    v3_orders_2(sK1)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f65,plain,(
% 1.87/0.99    v4_orders_2(sK1)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f66,plain,(
% 1.87/0.99    v5_orders_2(sK1)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f8,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f21,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f8])).
% 1.87/0.99  
% 1.87/0.99  fof(f22,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f21])).
% 1.87/0.99  
% 1.87/0.99  fof(f58,plain,(
% 1.87/0.99    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f70,plain,(
% 1.87/0.99    m2_orders_2(sK4,sK1,sK2)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f10,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f25,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f10])).
% 1.87/0.99  
% 1.87/0.99  fof(f26,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f25])).
% 1.87/0.99  
% 1.87/0.99  fof(f37,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(nnf_transformation,[],[f26])).
% 1.87/0.99  
% 1.87/0.99  fof(f62,plain,(
% 1.87/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f49,plain,(
% 1.87/0.99    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f34])).
% 1.87/0.99  
% 1.87/0.99  fof(f73,plain,(
% 1.87/0.99    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.87/0.99    inference(equality_resolution,[],[f49])).
% 1.87/0.99  
% 1.87/0.99  fof(f71,plain,(
% 1.87/0.99    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f7,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f19,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f7])).
% 1.87/0.99  
% 1.87/0.99  fof(f20,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f19])).
% 1.87/0.99  
% 1.87/0.99  fof(f57,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f20])).
% 1.87/0.99  
% 1.87/0.99  fof(f53,plain,(
% 1.87/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f36])).
% 1.87/0.99  
% 1.87/0.99  fof(f61,plain,(
% 1.87/0.99    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f50,plain,(
% 1.87/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f34])).
% 1.87/0.99  
% 1.87/0.99  fof(f72,plain,(
% 1.87/0.99    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f9,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f23,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f9])).
% 1.87/0.99  
% 1.87/0.99  fof(f24,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f23])).
% 1.87/0.99  
% 1.87/0.99  fof(f60,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f24])).
% 1.87/0.99  
% 1.87/0.99  fof(f1,axiom,(
% 1.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f14,plain,(
% 1.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f1])).
% 1.87/0.99  
% 1.87/0.99  fof(f29,plain,(
% 1.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.87/0.99    inference(nnf_transformation,[],[f14])).
% 1.87/0.99  
% 1.87/0.99  fof(f30,plain,(
% 1.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.87/0.99    inference(rectify,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f31,plain,(
% 1.87/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f32,plain,(
% 1.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.87/0.99  
% 1.87/0.99  fof(f45,plain,(
% 1.87/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f5,axiom,(
% 1.87/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f16,plain,(
% 1.87/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.87/0.99    inference(ennf_transformation,[],[f5])).
% 1.87/0.99  
% 1.87/0.99  fof(f55,plain,(
% 1.87/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  cnf(c_5,plain,
% 1.87/0.99      ( ~ r2_xboole_0(X0,X1) | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_9,plain,
% 1.87/0.99      ( r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_362,plain,
% 1.87/0.99      ( r1_tarski(X0,X1)
% 1.87/0.99      | X2 != X1
% 1.87/0.99      | k1_xboole_0 != X0
% 1.87/0.99      | k1_xboole_0 = X2 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_363,plain,
% 1.87/0.99      ( r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1478,plain,
% 1.87/0.99      ( k1_xboole_0 = X0 | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_8,plain,
% 1.87/0.99      ( r1_tarski(X0,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1482,plain,
% 1.87/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_21,negated_conjecture,
% 1.87/0.99      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.87/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1479,plain,
% 1.87/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_11,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_22,negated_conjecture,
% 1.87/0.99      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 1.87/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_469,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK2 != X2 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_470,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_469]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_23,negated_conjecture,
% 1.87/0.99      ( l1_orders_2(sK1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_809,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_470,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_810,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_809]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_27,negated_conjecture,
% 1.87/0.99      ( ~ v2_struct_0(sK1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_26,negated_conjecture,
% 1.87/0.99      ( v3_orders_2(sK1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_25,negated_conjecture,
% 1.87/0.99      ( v4_orders_2(sK1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_24,negated_conjecture,
% 1.87/0.99      ( v5_orders_2(sK1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_814,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_810,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_14,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_851,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | sK1 != X1
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_852,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1)
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_851]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_856,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_852,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_922,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(resolution,[status(thm)],[c_814,c_856]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_995,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(equality_resolution_simp,[status(thm)],[c_922]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1471,plain,
% 1.87/0.99      ( k1_xboole_0 = X0
% 1.87/0.99      | m1_orders_2(X0,sK1,X0) != iProver_top
% 1.87/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2568,plain,
% 1.87/0.99      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1479,c_1471]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_34,plain,
% 1.87/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1119,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1672,plain,
% 1.87/0.99      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1119]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2111,plain,
% 1.87/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1672]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1118,plain,( X0 = X0 ),theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2112,plain,
% 1.87/0.99      ( sK3 = sK3 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2154,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK3)
% 1.87/0.99      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.87/0.99      | k1_xboole_0 = sK3 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_995]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2159,plain,
% 1.87/0.99      ( k1_xboole_0 = sK3
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK3) != iProver_top
% 1.87/0.99      | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2154]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_20,negated_conjecture,
% 1.87/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1480,plain,
% 1.87/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_16,plain,
% 1.87/0.99      ( m1_orders_2(X0,X1,X2)
% 1.87/0.99      | m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.87/0.99      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_538,plain,
% 1.87/0.99      ( m1_orders_2(X0,X1,X2)
% 1.87/0.99      | m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK2 != X3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_539,plain,
% 1.87/0.99      ( m1_orders_2(X0,X1,X2)
% 1.87/0.99      | m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_749,plain,
% 1.87/0.99      ( m1_orders_2(X0,X1,X2)
% 1.87/0.99      | m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_539,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_750,plain,
% 1.87/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1)
% 1.87/0.99      | X0 = X1
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_749]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_754,plain,
% 1.87/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | X0 = X1
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_750,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1007,plain,
% 1.87/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | X0 = X1 ),
% 1.87/0.99      inference(equality_resolution_simp,[status(thm)],[c_754]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1468,plain,
% 1.87/0.99      ( X0 = X1
% 1.87/0.99      | m1_orders_2(X0,sK1,X1) = iProver_top
% 1.87/0.99      | m1_orders_2(X1,sK1,X0) = iProver_top
% 1.87/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.87/0.99      | m2_orders_2(X1,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1007]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1989,plain,
% 1.87/0.99      ( sK4 = X0
% 1.87/0.99      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 1.87/0.99      | m1_orders_2(sK4,sK1,X0) = iProver_top
% 1.87/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1480,c_1468]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2351,plain,
% 1.87/0.99      ( sK4 = sK3
% 1.87/0.99      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1479,c_1989]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_35,plain,
% 1.87/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4,plain,
% 1.87/0.99      ( ~ r2_xboole_0(X0,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_19,negated_conjecture,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_200,plain,
% 1.87/0.99      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 1.87/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_201,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_200]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_399,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_201]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_400,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_401,plain,
% 1.87/0.99      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1771,plain,
% 1.87/0.99      ( m1_orders_2(sK4,sK1,sK3)
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.87/0.99      | sK3 = sK4 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1007]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1775,plain,
% 1.87/0.99      ( sK3 = sK4
% 1.87/0.99      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.87/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.87/0.99      | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1771]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2360,plain,
% 1.87/0.99      ( m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2351,c_34,c_35,c_401,c_1775]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_12,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | r1_tarski(X0,X2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_872,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | r1_tarski(X0,X2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_873,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | r1_tarski(X0,X1)
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_872]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_875,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.87/0.99      | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_873,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_949,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m2_orders_2(X2,sK1,sK2)
% 1.87/0.99      | r1_tarski(X0,X1)
% 1.87/0.99      | X1 != X2
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_814,c_875]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_950,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | r1_tarski(X0,X1) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_949]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1472,plain,
% 1.87/0.99      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 1.87/0.99      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 1.87/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1710,plain,
% 1.87/0.99      ( m1_orders_2(X0,sK1,sK3) != iProver_top
% 1.87/0.99      | r1_tarski(X0,sK3) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1479,c_1472]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2366,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.87/0.99      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2360,c_1710]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_387,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | r1_tarski(X0,X1)
% 1.87/0.99      | sK4 != X1
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_201]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_388,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_387]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_389,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.87/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_6,plain,
% 1.87/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1777,plain,
% 1.87/0.99      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1778,plain,
% 1.87/0.99      ( sK3 = sK4
% 1.87/0.99      | r1_tarski(sK4,sK3) != iProver_top
% 1.87/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1777]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2445,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2366,c_389,c_401,c_1778]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_17,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.87/0.99      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_499,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK2 != X3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_500,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_499]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_779,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | X2 = X0
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_500,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_780,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1)
% 1.87/0.99      | X0 = X1
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_779]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_784,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | X0 = X1
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_780,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1003,plain,
% 1.87/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.87/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.87/0.99      | ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 1.87/0.99      | X0 = X1 ),
% 1.87/0.99      inference(equality_resolution_simp,[status(thm)],[c_784]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1469,plain,
% 1.87/0.99      ( X0 = X1
% 1.87/0.99      | m1_orders_2(X0,sK1,X1) != iProver_top
% 1.87/0.99      | m1_orders_2(X1,sK1,X0) != iProver_top
% 1.87/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.87/0.99      | m2_orders_2(X1,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1003]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1835,plain,
% 1.87/0.99      ( sK4 = X0
% 1.87/0.99      | m1_orders_2(X0,sK1,sK4) != iProver_top
% 1.87/0.99      | m1_orders_2(sK4,sK1,X0) != iProver_top
% 1.87/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1480,c_1469]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2214,plain,
% 1.87/0.99      ( sK4 = sK3
% 1.87/0.99      | m1_orders_2(sK4,sK1,sK3) != iProver_top
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1479,c_1835]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3,plain,
% 1.87/0.99      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_18,negated_conjecture,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_198,plain,
% 1.87/0.99      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 1.87/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_199,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_198]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_374,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | ~ r1_tarski(X0,X1)
% 1.87/0.99      | X1 = X0
% 1.87/0.99      | sK4 != X1
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_199]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_375,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_376,plain,
% 1.87/0.99      ( sK4 = sK3
% 1.87/0.99      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.87/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1629,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.87/0.99      | r1_tarski(sK3,sK4) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_950]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1630,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.87/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.87/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2282,plain,
% 1.87/0.99      ( sK4 = sK3 | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2214,c_35,c_376,c_1630]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2450,plain,
% 1.87/0.99      ( sK4 = sK3 ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2445,c_2282]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2456,plain,
% 1.87/0.99      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_2450,c_2445]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2727,plain,
% 1.87/0.99      ( sK3 = k1_xboole_0 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2568,c_34,c_2111,c_2112,c_2159,c_2456]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2734,plain,
% 1.87/0.99      ( m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_2727,c_1479]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_15,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.87/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_439,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.87/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK2 != X2 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_440,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(X1)),X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_830,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(X1)),X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v3_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v5_orders_2(X1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.87/0.99      | sK1 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_440,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_831,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)
% 1.87/0.99      | v2_struct_0(sK1)
% 1.87/0.99      | ~ v3_orders_2(sK1)
% 1.87/0.99      | ~ v4_orders_2(sK1)
% 1.87/0.99      | ~ v5_orders_2(sK1)
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_830]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_835,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)
% 1.87/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_831,c_27,c_26,c_25,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_999,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) ),
% 1.87/0.99      inference(equality_resolution_simp,[status(thm)],[c_835]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1470,plain,
% 1.87/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.87/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1484,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r2_hidden(X0,X2) = iProver_top
% 1.87/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2632,plain,
% 1.87/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.87/0.99      | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X1) = iProver_top
% 1.87/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1470,c_1484]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3361,plain,
% 1.87/0.99      ( r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) = iProver_top
% 1.87/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2734,c_2632]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_10,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1481,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3369,plain,
% 1.87/0.99      ( r1_tarski(X0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top
% 1.87/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_3361,c_1481]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3469,plain,
% 1.87/0.99      ( r1_tarski(k1_xboole_0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1482,c_3369]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3633,plain,
% 1.87/0.99      ( k1_funct_1(sK2,u1_struct_0(sK1)) = k1_xboole_0 ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1478,c_3469]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2090,plain,
% 1.87/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.87/0.99      | r1_tarski(X0,k1_funct_1(sK2,u1_struct_0(sK1))) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1470,c_1481]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3237,plain,
% 1.87/0.99      ( m2_orders_2(k1_funct_1(sK2,u1_struct_0(sK1)),sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1482,c_2090]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3764,plain,
% 1.87/0.99      ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_3633,c_3237]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1123,plain,
% 1.87/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.87/0.99      | m2_orders_2(X3,X4,X5)
% 1.87/0.99      | X3 != X0
% 1.87/0.99      | X4 != X1
% 1.87/0.99      | X5 != X2 ),
% 1.87/0.99      theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1642,plain,
% 1.87/0.99      ( m2_orders_2(X0,X1,X2)
% 1.87/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.87/0.99      | X2 != sK2
% 1.87/0.99      | X0 != sK4
% 1.87/0.99      | X1 != sK1 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1756,plain,
% 1.87/0.99      ( m2_orders_2(X0,X1,sK2)
% 1.87/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.87/0.99      | X0 != sK4
% 1.87/0.99      | X1 != sK1
% 1.87/0.99      | sK2 != sK2 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2257,plain,
% 1.87/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.87/0.99      | m2_orders_2(k1_xboole_0,X0,sK2)
% 1.87/0.99      | X0 != sK1
% 1.87/0.99      | sK2 != sK2
% 1.87/0.99      | k1_xboole_0 != sK4 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1756]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2259,plain,
% 1.87/0.99      ( X0 != sK1
% 1.87/0.99      | sK2 != sK2
% 1.87/0.99      | k1_xboole_0 != sK4
% 1.87/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.87/0.99      | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2257]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2261,plain,
% 1.87/0.99      ( sK2 != sK2
% 1.87/0.99      | sK1 != sK1
% 1.87/0.99      | k1_xboole_0 != sK4
% 1.87/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.87/0.99      | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_2259]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1780,plain,
% 1.87/0.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1119]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2126,plain,
% 1.87/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1780]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1757,plain,
% 1.87/0.99      ( sK2 = sK2 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_409,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | sK4 != X0
% 1.87/0.99      | sK3 != k1_xboole_0
% 1.87/0.99      | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_199]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_410,plain,
% 1.87/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.87/0.99      | sK3 != k1_xboole_0
% 1.87/0.99      | k1_xboole_0 = sK4 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_70,plain,
% 1.87/0.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_66,plain,
% 1.87/0.99      ( r1_tarski(sK1,sK1) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(contradiction,plain,
% 1.87/0.99      ( $false ),
% 1.87/0.99      inference(minisat,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_3764,c_2456,c_2445,c_2282,c_2261,c_2159,c_2126,c_2112,
% 1.87/0.99                 c_2111,c_1757,c_410,c_400,c_70,c_66,c_35,c_34]) ).
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  ------                               Statistics
% 1.87/0.99  
% 1.87/0.99  ------ General
% 1.87/0.99  
% 1.87/0.99  abstr_ref_over_cycles:                  0
% 1.87/0.99  abstr_ref_under_cycles:                 0
% 1.87/0.99  gc_basic_clause_elim:                   0
% 1.87/0.99  forced_gc_time:                         0
% 1.87/0.99  parsing_time:                           0.01
% 1.87/0.99  unif_index_cands_time:                  0.
% 1.87/0.99  unif_index_add_time:                    0.
% 1.87/0.99  orderings_time:                         0.
% 1.87/0.99  out_proof_time:                         0.024
% 1.87/0.99  total_time:                             0.128
% 1.87/0.99  num_of_symbols:                         53
% 1.87/0.99  num_of_terms:                           1963
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing
% 1.87/0.99  
% 1.87/0.99  num_of_splits:                          0
% 1.87/0.99  num_of_split_atoms:                     0
% 1.87/0.99  num_of_reused_defs:                     0
% 1.87/0.99  num_eq_ax_congr_red:                    12
% 1.87/0.99  num_of_sem_filtered_clauses:            1
% 1.87/0.99  num_of_subtypes:                        0
% 1.87/0.99  monotx_restored_types:                  0
% 1.87/0.99  sat_num_of_epr_types:                   0
% 1.87/0.99  sat_num_of_non_cyclic_types:            0
% 1.87/0.99  sat_guarded_non_collapsed_types:        0
% 1.87/0.99  num_pure_diseq_elim:                    0
% 1.87/0.99  simp_replaced_by:                       0
% 1.87/0.99  res_preprocessed:                       101
% 1.87/0.99  prep_upred:                             0
% 1.87/0.99  prep_unflattend:                        27
% 1.87/0.99  smt_new_axioms:                         0
% 1.87/0.99  pred_elim_cands:                        4
% 1.87/0.99  pred_elim:                              8
% 1.87/0.99  pred_elim_cl:                           8
% 1.87/0.99  pred_elim_cycles:                       11
% 1.87/0.99  merged_defs:                            2
% 1.87/0.99  merged_defs_ncl:                        0
% 1.87/0.99  bin_hyper_res:                          2
% 1.87/0.99  prep_cycles:                            4
% 1.87/0.99  pred_elim_time:                         0.014
% 1.87/0.99  splitting_time:                         0.
% 1.87/0.99  sem_filter_time:                        0.
% 1.87/0.99  monotx_time:                            0.001
% 1.87/0.99  subtype_inf_time:                       0.
% 1.87/0.99  
% 1.87/0.99  ------ Problem properties
% 1.87/0.99  
% 1.87/0.99  clauses:                                19
% 1.87/0.99  conjectures:                            2
% 1.87/0.99  epr:                                    16
% 1.87/0.99  horn:                                   15
% 1.87/0.99  ground:                                 7
% 1.87/0.99  unary:                                  3
% 1.87/0.99  binary:                                 8
% 1.87/0.99  lits:                                   47
% 1.87/0.99  lits_eq:                                9
% 1.87/0.99  fd_pure:                                0
% 1.87/0.99  fd_pseudo:                              0
% 1.87/0.99  fd_cond:                                2
% 1.87/0.99  fd_pseudo_cond:                         3
% 1.87/0.99  ac_symbols:                             0
% 1.87/0.99  
% 1.87/0.99  ------ Propositional Solver
% 1.87/0.99  
% 1.87/0.99  prop_solver_calls:                      27
% 1.87/0.99  prop_fast_solver_calls:                 878
% 1.87/0.99  smt_solver_calls:                       0
% 1.87/0.99  smt_fast_solver_calls:                  0
% 1.87/0.99  prop_num_of_clauses:                    1083
% 1.87/0.99  prop_preprocess_simplified:             3928
% 1.87/0.99  prop_fo_subsumed:                       35
% 1.87/0.99  prop_solver_time:                       0.
% 1.87/0.99  smt_solver_time:                        0.
% 1.87/0.99  smt_fast_solver_time:                   0.
% 1.87/0.99  prop_fast_solver_time:                  0.
% 1.87/0.99  prop_unsat_core_time:                   0.
% 1.87/0.99  
% 1.87/0.99  ------ QBF
% 1.87/0.99  
% 1.87/0.99  qbf_q_res:                              0
% 1.87/0.99  qbf_num_tautologies:                    0
% 1.87/0.99  qbf_prep_cycles:                        0
% 1.87/0.99  
% 1.87/0.99  ------ BMC1
% 1.87/0.99  
% 1.87/0.99  bmc1_current_bound:                     -1
% 1.87/0.99  bmc1_last_solved_bound:                 -1
% 1.87/0.99  bmc1_unsat_core_size:                   -1
% 1.87/0.99  bmc1_unsat_core_parents_size:           -1
% 1.87/0.99  bmc1_merge_next_fun:                    0
% 1.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation
% 1.87/0.99  
% 1.87/0.99  inst_num_of_clauses:                    302
% 1.87/0.99  inst_num_in_passive:                    74
% 1.87/0.99  inst_num_in_active:                     181
% 1.87/0.99  inst_num_in_unprocessed:                47
% 1.87/0.99  inst_num_of_loops:                      230
% 1.87/0.99  inst_num_of_learning_restarts:          0
% 1.87/0.99  inst_num_moves_active_passive:          46
% 1.87/0.99  inst_lit_activity:                      0
% 1.87/0.99  inst_lit_activity_moves:                0
% 1.87/0.99  inst_num_tautologies:                   0
% 1.87/0.99  inst_num_prop_implied:                  0
% 1.87/0.99  inst_num_existing_simplified:           0
% 1.87/0.99  inst_num_eq_res_simplified:             0
% 1.87/0.99  inst_num_child_elim:                    0
% 1.87/0.99  inst_num_of_dismatching_blockings:      118
% 1.87/0.99  inst_num_of_non_proper_insts:           388
% 1.87/0.99  inst_num_of_duplicates:                 0
% 1.87/0.99  inst_inst_num_from_inst_to_res:         0
% 1.87/0.99  inst_dismatching_checking_time:         0.
% 1.87/0.99  
% 1.87/0.99  ------ Resolution
% 1.87/0.99  
% 1.87/0.99  res_num_of_clauses:                     0
% 1.87/0.99  res_num_in_passive:                     0
% 1.87/0.99  res_num_in_active:                      0
% 1.87/0.99  res_num_of_loops:                       105
% 1.87/0.99  res_forward_subset_subsumed:            41
% 1.87/0.99  res_backward_subset_subsumed:           0
% 1.87/0.99  res_forward_subsumed:                   0
% 1.87/0.99  res_backward_subsumed:                  0
% 1.87/0.99  res_forward_subsumption_resolution:     0
% 1.87/0.99  res_backward_subsumption_resolution:    0
% 1.87/0.99  res_clause_to_clause_subsumption:       235
% 1.87/0.99  res_orphan_elimination:                 0
% 1.87/0.99  res_tautology_del:                      36
% 1.87/0.99  res_num_eq_res_simplified:              4
% 1.87/0.99  res_num_sel_changes:                    0
% 1.87/0.99  res_moves_from_active_to_pass:          0
% 1.87/0.99  
% 1.87/0.99  ------ Superposition
% 1.87/0.99  
% 1.87/0.99  sup_time_total:                         0.
% 1.87/0.99  sup_time_generating:                    0.
% 1.87/0.99  sup_time_sim_full:                      0.
% 1.87/0.99  sup_time_sim_immed:                     0.
% 1.87/0.99  
% 1.87/0.99  sup_num_of_clauses:                     38
% 1.87/0.99  sup_num_in_active:                      24
% 1.87/0.99  sup_num_in_passive:                     14
% 1.87/0.99  sup_num_of_loops:                       45
% 1.87/0.99  sup_fw_superposition:                   31
% 1.87/0.99  sup_bw_superposition:                   22
% 1.87/0.99  sup_immediate_simplified:               6
% 1.87/0.99  sup_given_eliminated:                   1
% 1.87/0.99  comparisons_done:                       0
% 1.87/0.99  comparisons_avoided:                    0
% 1.87/0.99  
% 1.87/0.99  ------ Simplifications
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  sim_fw_subset_subsumed:                 3
% 1.87/0.99  sim_bw_subset_subsumed:                 5
% 1.87/0.99  sim_fw_subsumed:                        2
% 1.87/0.99  sim_bw_subsumed:                        0
% 1.87/0.99  sim_fw_subsumption_res:                 0
% 1.87/0.99  sim_bw_subsumption_res:                 0
% 1.87/0.99  sim_tautology_del:                      1
% 1.87/0.99  sim_eq_tautology_del:                   8
% 1.87/0.99  sim_eq_res_simp:                        0
% 1.87/0.99  sim_fw_demodulated:                     0
% 1.87/0.99  sim_bw_demodulated:                     20
% 1.87/0.99  sim_light_normalised:                   3
% 1.87/0.99  sim_joinable_taut:                      0
% 1.87/0.99  sim_joinable_simp:                      0
% 1.87/0.99  sim_ac_normalised:                      0
% 1.87/0.99  sim_smt_subsumption:                    0
% 1.87/0.99  
%------------------------------------------------------------------------------
