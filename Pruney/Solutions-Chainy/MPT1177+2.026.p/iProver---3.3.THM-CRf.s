%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:52 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  185 (1347 expanded)
%              Number of clauses        :  117 ( 264 expanded)
%              Number of leaves         :   19 ( 435 expanded)
%              Depth                    :   20
%              Number of atoms          :  929 (12829 expanded)
%              Number of equality atoms :  194 ( 349 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40,f39,f38])).

fof(f68,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

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
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

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
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f44])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1476,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1475,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_490,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_491,plain,
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
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_701,plain,
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
    inference(resolution_lifted,[status(thm)],[c_491,c_23])).

cnf(c_702,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_706,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_27,c_26,c_25,c_24])).

cnf(c_880,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_706])).

cnf(c_1467,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_2753,plain,
    ( sK2 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_1467])).

cnf(c_35,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_73,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_210,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_211,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_408,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_211])).

cnf(c_409,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_410,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_562,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_563,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_680,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_563,c_23])).

cnf(c_681,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_685,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_27,c_26,c_25,c_24])).

cnf(c_884,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_685])).

cnf(c_1613,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1614,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1613])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_785,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_786,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_788,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_27,c_26,c_25,c_24])).

cnf(c_1629,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1630,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_1026,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1688,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1803,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1032,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1636,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X2 != sK3
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1802,plain,
    ( m1_orders_2(X0,X1,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X1 != sK0
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_2105,plain,
    ( m1_orders_2(sK3,X0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X0 != sK0
    | sK3 != sK3
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2106,plain,
    ( X0 != sK0
    | sK3 != sK3
    | sK3 != sK2
    | m1_orders_2(sK3,X0,sK3) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_2108,plain,
    ( sK3 != sK3
    | sK3 != sK2
    | sK0 != sK0
    | m1_orders_2(sK3,sK0,sK3) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_11])).

cnf(c_155,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_761,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_23])).

cnf(c_762,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_27,c_26,c_25,c_24])).

cnf(c_1700,plain,
    ( ~ m1_orders_2(X0,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_2839,plain,
    ( ~ m1_orders_2(sK3,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_2842,plain,
    ( k1_xboole_0 = sK3
    | m1_orders_2(sK3,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_1481,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1480,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2232,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1481,c_1480])).

cnf(c_10,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1477,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2992,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_1477])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_529,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_530,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_613,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 != X3
    | X0 != X5
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_530])).

cnf(c_614,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_656,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_614,c_23])).

cnf(c_657,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_27,c_26,c_25,c_24])).

cnf(c_888,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_661])).

cnf(c_1465,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | r1_tarski(X1,k4_xboole_0(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_3019,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2992,c_1465])).

cnf(c_2752,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1467])).

cnf(c_3072,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_2752])).

cnf(c_34,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_212,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_213,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_421,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_213])).

cnf(c_422,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_423,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_431,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_213])).

cnf(c_432,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_433,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_1616,plain,
    ( ~ m2_orders_2(sK2,sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1617,plain,
    ( m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_1787,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_2041,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_2042,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_1797,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2081,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_2082,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_2534,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2535,plain,
    ( m1_orders_2(sK3,sK0,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2534])).

cnf(c_3081,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3072,c_34,c_35,c_423,c_433,c_1617,c_2042,c_2082,c_2535])).

cnf(c_1033,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1641,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X2 != sK1
    | X0 != sK3
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_1687,plain,
    ( m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X0 != sK3
    | X1 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1641])).

cnf(c_3110,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,X0,sK1)
    | X0 != sK0
    | sK1 != sK1
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_3111,plain,
    ( X0 != sK0
    | sK1 != sK1
    | k1_xboole_0 != sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3110])).

cnf(c_3113,plain,
    ( sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3111])).

cnf(c_3143,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2753,c_34,c_35,c_73,c_77,c_410,c_423,c_433,c_1614,c_1617,c_1630,c_1688,c_1803,c_2042,c_2082,c_2108,c_2535,c_2842,c_3019,c_3113])).

cnf(c_3150,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1476,c_3143])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:05:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/0.98  
% 2.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.98  
% 2.50/0.98  ------  iProver source info
% 2.50/0.98  
% 2.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.98  git: non_committed_changes: false
% 2.50/0.98  git: last_make_outside_of_git: false
% 2.50/0.98  
% 2.50/0.98  ------ 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options
% 2.50/0.98  
% 2.50/0.98  --out_options                           all
% 2.50/0.98  --tptp_safe_out                         true
% 2.50/0.98  --problem_path                          ""
% 2.50/0.98  --include_path                          ""
% 2.50/0.98  --clausifier                            res/vclausify_rel
% 2.50/0.98  --clausifier_options                    --mode clausify
% 2.50/0.98  --stdin                                 false
% 2.50/0.98  --stats_out                             all
% 2.50/0.98  
% 2.50/0.98  ------ General Options
% 2.50/0.98  
% 2.50/0.98  --fof                                   false
% 2.50/0.98  --time_out_real                         305.
% 2.50/0.98  --time_out_virtual                      -1.
% 2.50/0.98  --symbol_type_check                     false
% 2.50/0.98  --clausify_out                          false
% 2.50/0.98  --sig_cnt_out                           false
% 2.50/0.98  --trig_cnt_out                          false
% 2.50/0.98  --trig_cnt_out_tolerance                1.
% 2.50/0.98  --trig_cnt_out_sk_spl                   false
% 2.50/0.98  --abstr_cl_out                          false
% 2.50/0.98  
% 2.50/0.98  ------ Global Options
% 2.50/0.98  
% 2.50/0.98  --schedule                              default
% 2.50/0.98  --add_important_lit                     false
% 2.50/0.98  --prop_solver_per_cl                    1000
% 2.50/0.98  --min_unsat_core                        false
% 2.50/0.98  --soft_assumptions                      false
% 2.50/0.98  --soft_lemma_size                       3
% 2.50/0.98  --prop_impl_unit_size                   0
% 2.50/0.98  --prop_impl_unit                        []
% 2.50/0.98  --share_sel_clauses                     true
% 2.50/0.98  --reset_solvers                         false
% 2.50/0.98  --bc_imp_inh                            [conj_cone]
% 2.50/0.98  --conj_cone_tolerance                   3.
% 2.50/0.98  --extra_neg_conj                        none
% 2.50/0.98  --large_theory_mode                     true
% 2.50/0.98  --prolific_symb_bound                   200
% 2.50/0.98  --lt_threshold                          2000
% 2.50/0.98  --clause_weak_htbl                      true
% 2.50/0.98  --gc_record_bc_elim                     false
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing Options
% 2.50/0.98  
% 2.50/0.98  --preprocessing_flag                    true
% 2.50/0.98  --time_out_prep_mult                    0.1
% 2.50/0.98  --splitting_mode                        input
% 2.50/0.98  --splitting_grd                         true
% 2.50/0.98  --splitting_cvd                         false
% 2.50/0.98  --splitting_cvd_svl                     false
% 2.50/0.98  --splitting_nvd                         32
% 2.50/0.98  --sub_typing                            true
% 2.50/0.98  --prep_gs_sim                           true
% 2.50/0.98  --prep_unflatten                        true
% 2.50/0.98  --prep_res_sim                          true
% 2.50/0.98  --prep_upred                            true
% 2.50/0.98  --prep_sem_filter                       exhaustive
% 2.50/0.98  --prep_sem_filter_out                   false
% 2.50/0.98  --pred_elim                             true
% 2.50/0.98  --res_sim_input                         true
% 2.50/0.98  --eq_ax_congr_red                       true
% 2.50/0.98  --pure_diseq_elim                       true
% 2.50/0.98  --brand_transform                       false
% 2.50/0.98  --non_eq_to_eq                          false
% 2.50/0.98  --prep_def_merge                        true
% 2.50/0.98  --prep_def_merge_prop_impl              false
% 2.50/0.98  --prep_def_merge_mbd                    true
% 2.50/0.98  --prep_def_merge_tr_red                 false
% 2.50/0.98  --prep_def_merge_tr_cl                  false
% 2.50/0.98  --smt_preprocessing                     true
% 2.50/0.98  --smt_ac_axioms                         fast
% 2.50/0.98  --preprocessed_out                      false
% 2.50/0.98  --preprocessed_stats                    false
% 2.50/0.98  
% 2.50/0.98  ------ Abstraction refinement Options
% 2.50/0.98  
% 2.50/0.98  --abstr_ref                             []
% 2.50/0.98  --abstr_ref_prep                        false
% 2.50/0.98  --abstr_ref_until_sat                   false
% 2.50/0.98  --abstr_ref_sig_restrict                funpre
% 2.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.98  --abstr_ref_under                       []
% 2.50/0.98  
% 2.50/0.98  ------ SAT Options
% 2.50/0.98  
% 2.50/0.98  --sat_mode                              false
% 2.50/0.98  --sat_fm_restart_options                ""
% 2.50/0.98  --sat_gr_def                            false
% 2.50/0.98  --sat_epr_types                         true
% 2.50/0.98  --sat_non_cyclic_types                  false
% 2.50/0.98  --sat_finite_models                     false
% 2.50/0.98  --sat_fm_lemmas                         false
% 2.50/0.98  --sat_fm_prep                           false
% 2.50/0.98  --sat_fm_uc_incr                        true
% 2.50/0.98  --sat_out_model                         small
% 2.50/0.98  --sat_out_clauses                       false
% 2.50/0.98  
% 2.50/0.98  ------ QBF Options
% 2.50/0.98  
% 2.50/0.98  --qbf_mode                              false
% 2.50/0.98  --qbf_elim_univ                         false
% 2.50/0.98  --qbf_dom_inst                          none
% 2.50/0.98  --qbf_dom_pre_inst                      false
% 2.50/0.98  --qbf_sk_in                             false
% 2.50/0.98  --qbf_pred_elim                         true
% 2.50/0.98  --qbf_split                             512
% 2.50/0.98  
% 2.50/0.98  ------ BMC1 Options
% 2.50/0.98  
% 2.50/0.98  --bmc1_incremental                      false
% 2.50/0.98  --bmc1_axioms                           reachable_all
% 2.50/0.98  --bmc1_min_bound                        0
% 2.50/0.98  --bmc1_max_bound                        -1
% 2.50/0.98  --bmc1_max_bound_default                -1
% 2.50/0.98  --bmc1_symbol_reachability              true
% 2.50/0.98  --bmc1_property_lemmas                  false
% 2.50/0.98  --bmc1_k_induction                      false
% 2.50/0.98  --bmc1_non_equiv_states                 false
% 2.50/0.98  --bmc1_deadlock                         false
% 2.50/0.98  --bmc1_ucm                              false
% 2.50/0.98  --bmc1_add_unsat_core                   none
% 2.50/0.98  --bmc1_unsat_core_children              false
% 2.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.98  --bmc1_out_stat                         full
% 2.50/0.98  --bmc1_ground_init                      false
% 2.50/0.98  --bmc1_pre_inst_next_state              false
% 2.50/0.98  --bmc1_pre_inst_state                   false
% 2.50/0.98  --bmc1_pre_inst_reach_state             false
% 2.50/0.98  --bmc1_out_unsat_core                   false
% 2.50/0.98  --bmc1_aig_witness_out                  false
% 2.50/0.98  --bmc1_verbose                          false
% 2.50/0.98  --bmc1_dump_clauses_tptp                false
% 2.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.98  --bmc1_dump_file                        -
% 2.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.98  --bmc1_ucm_extend_mode                  1
% 2.50/0.98  --bmc1_ucm_init_mode                    2
% 2.50/0.98  --bmc1_ucm_cone_mode                    none
% 2.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.98  --bmc1_ucm_relax_model                  4
% 2.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.98  --bmc1_ucm_layered_model                none
% 2.50/0.98  --bmc1_ucm_max_lemma_size               10
% 2.50/0.98  
% 2.50/0.98  ------ AIG Options
% 2.50/0.98  
% 2.50/0.98  --aig_mode                              false
% 2.50/0.98  
% 2.50/0.98  ------ Instantiation Options
% 2.50/0.98  
% 2.50/0.98  --instantiation_flag                    true
% 2.50/0.98  --inst_sos_flag                         false
% 2.50/0.98  --inst_sos_phase                        true
% 2.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel_side                     num_symb
% 2.50/0.98  --inst_solver_per_active                1400
% 2.50/0.98  --inst_solver_calls_frac                1.
% 2.50/0.98  --inst_passive_queue_type               priority_queues
% 2.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.98  --inst_passive_queues_freq              [25;2]
% 2.50/0.98  --inst_dismatching                      true
% 2.50/0.98  --inst_eager_unprocessed_to_passive     true
% 2.50/0.98  --inst_prop_sim_given                   true
% 2.50/0.98  --inst_prop_sim_new                     false
% 2.50/0.98  --inst_subs_new                         false
% 2.50/0.98  --inst_eq_res_simp                      false
% 2.50/0.98  --inst_subs_given                       false
% 2.50/0.98  --inst_orphan_elimination               true
% 2.50/0.98  --inst_learning_loop_flag               true
% 2.50/0.98  --inst_learning_start                   3000
% 2.50/0.98  --inst_learning_factor                  2
% 2.50/0.98  --inst_start_prop_sim_after_learn       3
% 2.50/0.98  --inst_sel_renew                        solver
% 2.50/0.98  --inst_lit_activity_flag                true
% 2.50/0.98  --inst_restr_to_given                   false
% 2.50/0.98  --inst_activity_threshold               500
% 2.50/0.98  --inst_out_proof                        true
% 2.50/0.98  
% 2.50/0.98  ------ Resolution Options
% 2.50/0.98  
% 2.50/0.98  --resolution_flag                       true
% 2.50/0.98  --res_lit_sel                           adaptive
% 2.50/0.98  --res_lit_sel_side                      none
% 2.50/0.98  --res_ordering                          kbo
% 2.50/0.98  --res_to_prop_solver                    active
% 2.50/0.98  --res_prop_simpl_new                    false
% 2.50/0.98  --res_prop_simpl_given                  true
% 2.50/0.98  --res_passive_queue_type                priority_queues
% 2.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.98  --res_passive_queues_freq               [15;5]
% 2.50/0.98  --res_forward_subs                      full
% 2.50/0.98  --res_backward_subs                     full
% 2.50/0.98  --res_forward_subs_resolution           true
% 2.50/0.98  --res_backward_subs_resolution          true
% 2.50/0.98  --res_orphan_elimination                true
% 2.50/0.98  --res_time_limit                        2.
% 2.50/0.98  --res_out_proof                         true
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Options
% 2.50/0.98  
% 2.50/0.98  --superposition_flag                    true
% 2.50/0.98  --sup_passive_queue_type                priority_queues
% 2.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.98  --demod_completeness_check              fast
% 2.50/0.98  --demod_use_ground                      true
% 2.50/0.98  --sup_to_prop_solver                    passive
% 2.50/0.98  --sup_prop_simpl_new                    true
% 2.50/0.98  --sup_prop_simpl_given                  true
% 2.50/0.98  --sup_fun_splitting                     false
% 2.50/0.98  --sup_smt_interval                      50000
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Simplification Setup
% 2.50/0.98  
% 2.50/0.98  --sup_indices_passive                   []
% 2.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_full_bw                           [BwDemod]
% 2.50/0.98  --sup_immed_triv                        [TrivRules]
% 2.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_immed_bw_main                     []
% 2.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  
% 2.50/0.98  ------ Combination Options
% 2.50/0.98  
% 2.50/0.98  --comb_res_mult                         3
% 2.50/0.98  --comb_sup_mult                         2
% 2.50/0.98  --comb_inst_mult                        10
% 2.50/0.98  
% 2.50/0.98  ------ Debug Options
% 2.50/0.98  
% 2.50/0.98  --dbg_backtrace                         false
% 2.50/0.98  --dbg_dump_prop_clauses                 false
% 2.50/0.98  --dbg_dump_prop_clauses_file            -
% 2.50/0.98  --dbg_out_stat                          false
% 2.50/0.98  ------ Parsing...
% 2.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.98  ------ Proving...
% 2.50/0.98  ------ Problem Properties 
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  clauses                                 18
% 2.50/0.98  conjectures                             2
% 2.50/0.98  EPR                                     9
% 2.50/0.98  Horn                                    16
% 2.50/0.98  unary                                   4
% 2.50/0.98  binary                                  6
% 2.50/0.98  lits                                    45
% 2.50/0.98  lits eq                                 8
% 2.50/0.98  fd_pure                                 0
% 2.50/0.98  fd_pseudo                               0
% 2.50/0.98  fd_cond                                 1
% 2.50/0.98  fd_pseudo_cond                          3
% 2.50/0.98  AC symbols                              0
% 2.50/0.98  
% 2.50/0.98  ------ Schedule dynamic 5 is on 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  ------ 
% 2.50/0.98  Current options:
% 2.50/0.98  ------ 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options
% 2.50/0.98  
% 2.50/0.98  --out_options                           all
% 2.50/0.98  --tptp_safe_out                         true
% 2.50/0.98  --problem_path                          ""
% 2.50/0.98  --include_path                          ""
% 2.50/0.98  --clausifier                            res/vclausify_rel
% 2.50/0.98  --clausifier_options                    --mode clausify
% 2.50/0.98  --stdin                                 false
% 2.50/0.98  --stats_out                             all
% 2.50/0.98  
% 2.50/0.98  ------ General Options
% 2.50/0.98  
% 2.50/0.98  --fof                                   false
% 2.50/0.98  --time_out_real                         305.
% 2.50/0.98  --time_out_virtual                      -1.
% 2.50/0.98  --symbol_type_check                     false
% 2.50/0.98  --clausify_out                          false
% 2.50/0.98  --sig_cnt_out                           false
% 2.50/0.98  --trig_cnt_out                          false
% 2.50/0.98  --trig_cnt_out_tolerance                1.
% 2.50/0.98  --trig_cnt_out_sk_spl                   false
% 2.50/0.98  --abstr_cl_out                          false
% 2.50/0.98  
% 2.50/0.98  ------ Global Options
% 2.50/0.98  
% 2.50/0.98  --schedule                              default
% 2.50/0.98  --add_important_lit                     false
% 2.50/0.98  --prop_solver_per_cl                    1000
% 2.50/0.98  --min_unsat_core                        false
% 2.50/0.98  --soft_assumptions                      false
% 2.50/0.98  --soft_lemma_size                       3
% 2.50/0.98  --prop_impl_unit_size                   0
% 2.50/0.98  --prop_impl_unit                        []
% 2.50/0.98  --share_sel_clauses                     true
% 2.50/0.98  --reset_solvers                         false
% 2.50/0.98  --bc_imp_inh                            [conj_cone]
% 2.50/0.98  --conj_cone_tolerance                   3.
% 2.50/0.98  --extra_neg_conj                        none
% 2.50/0.98  --large_theory_mode                     true
% 2.50/0.98  --prolific_symb_bound                   200
% 2.50/0.98  --lt_threshold                          2000
% 2.50/0.98  --clause_weak_htbl                      true
% 2.50/0.98  --gc_record_bc_elim                     false
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing Options
% 2.50/0.98  
% 2.50/0.98  --preprocessing_flag                    true
% 2.50/0.98  --time_out_prep_mult                    0.1
% 2.50/0.98  --splitting_mode                        input
% 2.50/0.98  --splitting_grd                         true
% 2.50/0.98  --splitting_cvd                         false
% 2.50/0.98  --splitting_cvd_svl                     false
% 2.50/0.98  --splitting_nvd                         32
% 2.50/0.98  --sub_typing                            true
% 2.50/0.98  --prep_gs_sim                           true
% 2.50/0.98  --prep_unflatten                        true
% 2.50/0.98  --prep_res_sim                          true
% 2.50/0.98  --prep_upred                            true
% 2.50/0.98  --prep_sem_filter                       exhaustive
% 2.50/0.98  --prep_sem_filter_out                   false
% 2.50/0.98  --pred_elim                             true
% 2.50/0.98  --res_sim_input                         true
% 2.50/0.98  --eq_ax_congr_red                       true
% 2.50/0.98  --pure_diseq_elim                       true
% 2.50/0.98  --brand_transform                       false
% 2.50/0.98  --non_eq_to_eq                          false
% 2.50/0.98  --prep_def_merge                        true
% 2.50/0.98  --prep_def_merge_prop_impl              false
% 2.50/0.98  --prep_def_merge_mbd                    true
% 2.50/0.98  --prep_def_merge_tr_red                 false
% 2.50/0.98  --prep_def_merge_tr_cl                  false
% 2.50/0.98  --smt_preprocessing                     true
% 2.50/0.98  --smt_ac_axioms                         fast
% 2.50/0.98  --preprocessed_out                      false
% 2.50/0.98  --preprocessed_stats                    false
% 2.50/0.98  
% 2.50/0.98  ------ Abstraction refinement Options
% 2.50/0.98  
% 2.50/0.98  --abstr_ref                             []
% 2.50/0.98  --abstr_ref_prep                        false
% 2.50/0.98  --abstr_ref_until_sat                   false
% 2.50/0.98  --abstr_ref_sig_restrict                funpre
% 2.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.98  --abstr_ref_under                       []
% 2.50/0.98  
% 2.50/0.98  ------ SAT Options
% 2.50/0.98  
% 2.50/0.98  --sat_mode                              false
% 2.50/0.98  --sat_fm_restart_options                ""
% 2.50/0.98  --sat_gr_def                            false
% 2.50/0.98  --sat_epr_types                         true
% 2.50/0.98  --sat_non_cyclic_types                  false
% 2.50/0.98  --sat_finite_models                     false
% 2.50/0.98  --sat_fm_lemmas                         false
% 2.50/0.98  --sat_fm_prep                           false
% 2.50/0.98  --sat_fm_uc_incr                        true
% 2.50/0.98  --sat_out_model                         small
% 2.50/0.98  --sat_out_clauses                       false
% 2.50/0.98  
% 2.50/0.98  ------ QBF Options
% 2.50/0.98  
% 2.50/0.98  --qbf_mode                              false
% 2.50/0.98  --qbf_elim_univ                         false
% 2.50/0.98  --qbf_dom_inst                          none
% 2.50/0.98  --qbf_dom_pre_inst                      false
% 2.50/0.98  --qbf_sk_in                             false
% 2.50/0.98  --qbf_pred_elim                         true
% 2.50/0.98  --qbf_split                             512
% 2.50/0.98  
% 2.50/0.98  ------ BMC1 Options
% 2.50/0.98  
% 2.50/0.98  --bmc1_incremental                      false
% 2.50/0.98  --bmc1_axioms                           reachable_all
% 2.50/0.98  --bmc1_min_bound                        0
% 2.50/0.98  --bmc1_max_bound                        -1
% 2.50/0.98  --bmc1_max_bound_default                -1
% 2.50/0.98  --bmc1_symbol_reachability              true
% 2.50/0.98  --bmc1_property_lemmas                  false
% 2.50/0.98  --bmc1_k_induction                      false
% 2.50/0.98  --bmc1_non_equiv_states                 false
% 2.50/0.98  --bmc1_deadlock                         false
% 2.50/0.98  --bmc1_ucm                              false
% 2.50/0.98  --bmc1_add_unsat_core                   none
% 2.50/0.98  --bmc1_unsat_core_children              false
% 2.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.98  --bmc1_out_stat                         full
% 2.50/0.98  --bmc1_ground_init                      false
% 2.50/0.98  --bmc1_pre_inst_next_state              false
% 2.50/0.98  --bmc1_pre_inst_state                   false
% 2.50/0.98  --bmc1_pre_inst_reach_state             false
% 2.50/0.98  --bmc1_out_unsat_core                   false
% 2.50/0.98  --bmc1_aig_witness_out                  false
% 2.50/0.98  --bmc1_verbose                          false
% 2.50/0.98  --bmc1_dump_clauses_tptp                false
% 2.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.98  --bmc1_dump_file                        -
% 2.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.98  --bmc1_ucm_extend_mode                  1
% 2.50/0.98  --bmc1_ucm_init_mode                    2
% 2.50/0.98  --bmc1_ucm_cone_mode                    none
% 2.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.98  --bmc1_ucm_relax_model                  4
% 2.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.98  --bmc1_ucm_layered_model                none
% 2.50/0.98  --bmc1_ucm_max_lemma_size               10
% 2.50/0.98  
% 2.50/0.98  ------ AIG Options
% 2.50/0.98  
% 2.50/0.98  --aig_mode                              false
% 2.50/0.98  
% 2.50/0.98  ------ Instantiation Options
% 2.50/0.98  
% 2.50/0.98  --instantiation_flag                    true
% 2.50/0.98  --inst_sos_flag                         false
% 2.50/0.98  --inst_sos_phase                        true
% 2.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel_side                     none
% 2.50/0.98  --inst_solver_per_active                1400
% 2.50/0.98  --inst_solver_calls_frac                1.
% 2.50/0.98  --inst_passive_queue_type               priority_queues
% 2.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.98  --inst_passive_queues_freq              [25;2]
% 2.50/0.98  --inst_dismatching                      true
% 2.50/0.98  --inst_eager_unprocessed_to_passive     true
% 2.50/0.98  --inst_prop_sim_given                   true
% 2.50/0.98  --inst_prop_sim_new                     false
% 2.50/0.98  --inst_subs_new                         false
% 2.50/0.98  --inst_eq_res_simp                      false
% 2.50/0.98  --inst_subs_given                       false
% 2.50/0.98  --inst_orphan_elimination               true
% 2.50/0.98  --inst_learning_loop_flag               true
% 2.50/0.98  --inst_learning_start                   3000
% 2.50/0.98  --inst_learning_factor                  2
% 2.50/0.98  --inst_start_prop_sim_after_learn       3
% 2.50/0.98  --inst_sel_renew                        solver
% 2.50/0.98  --inst_lit_activity_flag                true
% 2.50/0.98  --inst_restr_to_given                   false
% 2.50/0.98  --inst_activity_threshold               500
% 2.50/0.98  --inst_out_proof                        true
% 2.50/0.98  
% 2.50/0.98  ------ Resolution Options
% 2.50/0.98  
% 2.50/0.98  --resolution_flag                       false
% 2.50/0.98  --res_lit_sel                           adaptive
% 2.50/0.98  --res_lit_sel_side                      none
% 2.50/0.98  --res_ordering                          kbo
% 2.50/0.98  --res_to_prop_solver                    active
% 2.50/0.98  --res_prop_simpl_new                    false
% 2.50/0.98  --res_prop_simpl_given                  true
% 2.50/0.98  --res_passive_queue_type                priority_queues
% 2.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.98  --res_passive_queues_freq               [15;5]
% 2.50/0.98  --res_forward_subs                      full
% 2.50/0.98  --res_backward_subs                     full
% 2.50/0.98  --res_forward_subs_resolution           true
% 2.50/0.98  --res_backward_subs_resolution          true
% 2.50/0.98  --res_orphan_elimination                true
% 2.50/0.98  --res_time_limit                        2.
% 2.50/0.98  --res_out_proof                         true
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Options
% 2.50/0.98  
% 2.50/0.98  --superposition_flag                    true
% 2.50/0.98  --sup_passive_queue_type                priority_queues
% 2.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.98  --demod_completeness_check              fast
% 2.50/0.98  --demod_use_ground                      true
% 2.50/0.98  --sup_to_prop_solver                    passive
% 2.50/0.98  --sup_prop_simpl_new                    true
% 2.50/0.98  --sup_prop_simpl_given                  true
% 2.50/0.98  --sup_fun_splitting                     false
% 2.50/0.98  --sup_smt_interval                      50000
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Simplification Setup
% 2.50/0.98  
% 2.50/0.98  --sup_indices_passive                   []
% 2.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_full_bw                           [BwDemod]
% 2.50/0.98  --sup_immed_triv                        [TrivRules]
% 2.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_immed_bw_main                     []
% 2.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  
% 2.50/0.98  ------ Combination Options
% 2.50/0.98  
% 2.50/0.98  --comb_res_mult                         3
% 2.50/0.98  --comb_sup_mult                         2
% 2.50/0.98  --comb_inst_mult                        10
% 2.50/0.98  
% 2.50/0.98  ------ Debug Options
% 2.50/0.98  
% 2.50/0.98  --dbg_backtrace                         false
% 2.50/0.98  --dbg_dump_prop_clauses                 false
% 2.50/0.98  --dbg_dump_prop_clauses_file            -
% 2.50/0.98  --dbg_out_stat                          false
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  ------ Proving...
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  % SZS status Theorem for theBenchmark.p
% 2.50/0.98  
% 2.50/0.98   Resolution empty clause
% 2.50/0.98  
% 2.50/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.98  
% 2.50/0.98  fof(f12,conjecture,(
% 2.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f13,negated_conjecture,(
% 2.50/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.50/0.98    inference(negated_conjecture,[],[f12])).
% 2.50/0.98  
% 2.50/0.98  fof(f28,plain,(
% 2.50/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f13])).
% 2.50/0.98  
% 2.50/0.98  fof(f29,plain,(
% 2.50/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f28])).
% 2.50/0.98  
% 2.50/0.98  fof(f36,plain,(
% 2.50/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.50/0.98    inference(nnf_transformation,[],[f29])).
% 2.50/0.98  
% 2.50/0.98  fof(f37,plain,(
% 2.50/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f36])).
% 2.50/0.98  
% 2.50/0.98  fof(f41,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.50/0.98    introduced(choice_axiom,[])).
% 2.50/0.98  
% 2.50/0.98  fof(f40,plain,(
% 2.50/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.50/0.98    introduced(choice_axiom,[])).
% 2.50/0.98  
% 2.50/0.98  fof(f39,plain,(
% 2.50/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.50/0.98    introduced(choice_axiom,[])).
% 2.50/0.98  
% 2.50/0.98  fof(f38,plain,(
% 2.50/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.50/0.98    introduced(choice_axiom,[])).
% 2.50/0.98  
% 2.50/0.98  fof(f42,plain,(
% 2.50/0.98    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40,f39,f38])).
% 2.50/0.98  
% 2.50/0.98  fof(f68,plain,(
% 2.50/0.98    m2_orders_2(sK3,sK0,sK1)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f67,plain,(
% 2.50/0.98    m2_orders_2(sK2,sK0,sK1)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f11,axiom,(
% 2.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f26,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f11])).
% 2.50/0.98  
% 2.50/0.98  fof(f27,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f26])).
% 2.50/0.98  
% 2.50/0.98  fof(f35,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(nnf_transformation,[],[f27])).
% 2.50/0.98  
% 2.50/0.98  fof(f60,plain,(
% 2.50/0.98    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f35])).
% 2.50/0.98  
% 2.50/0.98  fof(f66,plain,(
% 2.50/0.98    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f65,plain,(
% 2.50/0.98    l1_orders_2(sK0)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f61,plain,(
% 2.50/0.98    ~v2_struct_0(sK0)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f62,plain,(
% 2.50/0.98    v3_orders_2(sK0)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f63,plain,(
% 2.50/0.98    v4_orders_2(sK0)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f64,plain,(
% 2.50/0.98    v5_orders_2(sK0)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f2,axiom,(
% 2.50/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f32,plain,(
% 2.50/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.50/0.98    inference(nnf_transformation,[],[f2])).
% 2.50/0.98  
% 2.50/0.98  fof(f33,plain,(
% 2.50/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.50/0.98    inference(flattening,[],[f32])).
% 2.50/0.98  
% 2.50/0.98  fof(f46,plain,(
% 2.50/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.50/0.98    inference(cnf_transformation,[],[f33])).
% 2.50/0.98  
% 2.50/0.98  fof(f73,plain,(
% 2.50/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.50/0.98    inference(equality_resolution,[],[f46])).
% 2.50/0.98  
% 2.50/0.98  fof(f48,plain,(
% 2.50/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f33])).
% 2.50/0.98  
% 2.50/0.98  fof(f1,axiom,(
% 2.50/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f30,plain,(
% 2.50/0.98    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.50/0.98    inference(nnf_transformation,[],[f1])).
% 2.50/0.98  
% 2.50/0.98  fof(f31,plain,(
% 2.50/0.98    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.50/0.98    inference(flattening,[],[f30])).
% 2.50/0.98  
% 2.50/0.98  fof(f45,plain,(
% 2.50/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f31])).
% 2.50/0.98  
% 2.50/0.98  fof(f70,plain,(
% 2.50/0.98    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f7,axiom,(
% 2.50/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f14,plain,(
% 2.50/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.98    inference(pure_predicate_removal,[],[f7])).
% 2.50/0.98  
% 2.50/0.98  fof(f18,plain,(
% 2.50/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f14])).
% 2.50/0.98  
% 2.50/0.98  fof(f19,plain,(
% 2.50/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f18])).
% 2.50/0.98  
% 2.50/0.98  fof(f55,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f19])).
% 2.50/0.98  
% 2.50/0.98  fof(f8,axiom,(
% 2.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f20,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f8])).
% 2.50/0.98  
% 2.50/0.98  fof(f21,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f20])).
% 2.50/0.98  
% 2.50/0.98  fof(f56,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f21])).
% 2.50/0.98  
% 2.50/0.98  fof(f9,axiom,(
% 2.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f22,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f9])).
% 2.50/0.98  
% 2.50/0.98  fof(f23,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f22])).
% 2.50/0.98  
% 2.50/0.98  fof(f57,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f23])).
% 2.50/0.98  
% 2.50/0.98  fof(f6,axiom,(
% 2.50/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f16,plain,(
% 2.50/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f6])).
% 2.50/0.98  
% 2.50/0.98  fof(f17,plain,(
% 2.50/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f16])).
% 2.50/0.98  
% 2.50/0.98  fof(f54,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f17])).
% 2.50/0.98  
% 2.50/0.98  fof(f3,axiom,(
% 2.50/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f34,plain,(
% 2.50/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.50/0.98    inference(nnf_transformation,[],[f3])).
% 2.50/0.98  
% 2.50/0.98  fof(f50,plain,(
% 2.50/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f34])).
% 2.50/0.98  
% 2.50/0.98  fof(f5,axiom,(
% 2.50/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f53,plain,(
% 2.50/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f5])).
% 2.50/0.98  
% 2.50/0.98  fof(f4,axiom,(
% 2.50/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f15,plain,(
% 2.50/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.50/0.98    inference(ennf_transformation,[],[f4])).
% 2.50/0.98  
% 2.50/0.98  fof(f52,plain,(
% 2.50/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.50/0.98    inference(cnf_transformation,[],[f15])).
% 2.50/0.98  
% 2.50/0.98  fof(f10,axiom,(
% 2.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.98  
% 2.50/0.98  fof(f24,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.50/0.98    inference(ennf_transformation,[],[f10])).
% 2.50/0.98  
% 2.50/0.98  fof(f25,plain,(
% 2.50/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.50/0.98    inference(flattening,[],[f24])).
% 2.50/0.98  
% 2.50/0.98  fof(f58,plain,(
% 2.50/0.98    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f25])).
% 2.50/0.98  
% 2.50/0.98  fof(f43,plain,(
% 2.50/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f31])).
% 2.50/0.98  
% 2.50/0.98  fof(f69,plain,(
% 2.50/0.98    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.50/0.98    inference(cnf_transformation,[],[f42])).
% 2.50/0.98  
% 2.50/0.98  fof(f44,plain,(
% 2.50/0.98    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.50/0.98    inference(cnf_transformation,[],[f31])).
% 2.50/0.98  
% 2.50/0.98  fof(f71,plain,(
% 2.50/0.98    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.50/0.98    inference(equality_resolution,[],[f44])).
% 2.50/0.98  
% 2.50/0.98  cnf(c_20,negated_conjecture,
% 2.50/0.98      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.50/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_1476,plain,
% 2.50/0.98      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_21,negated_conjecture,
% 2.50/0.98      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.50/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.50/0.98  
% 2.50/0.98  cnf(c_1475,plain,
% 2.50/0.98      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.50/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_16,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.50/0.99      | m1_orders_2(X3,X1,X0)
% 2.50/0.99      | m1_orders_2(X0,X1,X3)
% 2.50/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | X3 = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_22,negated_conjecture,
% 2.50/0.99      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.50/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_490,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.50/0.99      | m1_orders_2(X3,X1,X0)
% 2.50/0.99      | m1_orders_2(X0,X1,X3)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | X3 = X0
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK1 != X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_491,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | m1_orders_2(X0,X1,X2)
% 2.50/0.99      | m1_orders_2(X2,X1,X0)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | X0 = X2
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_23,negated_conjecture,
% 2.50/0.99      ( l1_orders_2(sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_701,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | m1_orders_2(X0,X1,X2)
% 2.50/0.99      | m1_orders_2(X2,X1,X0)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | X2 = X0
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK0 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_491,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_702,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | m1_orders_2(X1,sK0,X0)
% 2.50/0.99      | v2_struct_0(sK0)
% 2.50/0.99      | ~ v3_orders_2(sK0)
% 2.50/0.99      | ~ v4_orders_2(sK0)
% 2.50/0.99      | ~ v5_orders_2(sK0)
% 2.50/0.99      | X0 = X1
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_701]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_27,negated_conjecture,
% 2.50/0.99      ( ~ v2_struct_0(sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_26,negated_conjecture,
% 2.50/0.99      ( v3_orders_2(sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_25,negated_conjecture,
% 2.50/0.99      ( v4_orders_2(sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_24,negated_conjecture,
% 2.50/0.99      ( v5_orders_2(sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_706,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | m1_orders_2(X1,sK0,X0)
% 2.50/0.99      | X0 = X1
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_702,c_27,c_26,c_25,c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_880,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | m1_orders_2(X1,sK0,X0)
% 2.50/0.99      | X0 = X1 ),
% 2.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_706]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1467,plain,
% 2.50/0.99      ( X0 = X1
% 2.50/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.50/0.99      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2753,plain,
% 2.50/0.99      ( sK2 = X0
% 2.50/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_orders_2(X0,sK0,sK2) = iProver_top
% 2.50/0.99      | m1_orders_2(sK2,sK0,X0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1475,c_1467]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_35,plain,
% 2.50/0.99      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f73]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_73,plain,
% 2.50/0.99      ( r1_tarski(sK0,sK0) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_77,plain,
% 2.50/0.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_0,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_18,negated_conjecture,
% 2.50/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_210,plain,
% 2.50/0.99      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.50/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_211,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_408,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | ~ r1_tarski(X0,X1)
% 2.50/0.99      | X1 = X0
% 2.50/0.99      | sK3 != X1
% 2.50/0.99      | sK2 != X0 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_211]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_409,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_410,plain,
% 2.50/0.99      ( sK3 = sK2
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.50/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_12,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_562,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK1 != X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_563,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_562]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_680,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK0 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_563,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_681,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | v2_struct_0(sK0)
% 2.50/0.99      | ~ v3_orders_2(sK0)
% 2.50/0.99      | ~ v4_orders_2(sK0)
% 2.50/0.99      | ~ v5_orders_2(sK0)
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_680]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_685,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_681,c_27,c_26,c_25,c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_884,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_685]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1613,plain,
% 2.50/0.99      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_884]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1614,plain,
% 2.50/0.99      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1613]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_13,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | r1_tarski(X0,X2)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_785,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | r1_tarski(X0,X2)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | sK0 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_786,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | r1_tarski(X0,X1)
% 2.50/0.99      | v2_struct_0(sK0)
% 2.50/0.99      | ~ v3_orders_2(sK0)
% 2.50/0.99      | ~ v4_orders_2(sK0)
% 2.50/0.99      | ~ v5_orders_2(sK0) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_785]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_788,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | r1_tarski(X0,X1) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_786,c_27,c_26,c_25,c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1629,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | r1_tarski(sK2,sK3) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_788]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1630,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.50/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1026,plain,( X0 = X0 ),theory(equality) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1688,plain,
% 2.50/0.99      ( sK1 = sK1 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1803,plain,
% 2.50/0.99      ( sK3 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1032,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | m1_orders_2(X3,X4,X5)
% 2.50/0.99      | X3 != X0
% 2.50/0.99      | X4 != X1
% 2.50/0.99      | X5 != X2 ),
% 2.50/0.99      theory(equality) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1636,plain,
% 2.50/0.99      ( m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | X2 != sK3
% 2.50/0.99      | X1 != sK0
% 2.50/0.99      | X0 != sK2 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1032]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1802,plain,
% 2.50/0.99      ( m1_orders_2(X0,X1,sK3)
% 2.50/0.99      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | X1 != sK0
% 2.50/0.99      | X0 != sK2
% 2.50/0.99      | sK3 != sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1636]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2105,plain,
% 2.50/0.99      ( m1_orders_2(sK3,X0,sK3)
% 2.50/0.99      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | X0 != sK0
% 2.50/0.99      | sK3 != sK3
% 2.50/0.99      | sK3 != sK2 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1802]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2106,plain,
% 2.50/0.99      ( X0 != sK0
% 2.50/0.99      | sK3 != sK3
% 2.50/0.99      | sK3 != sK2
% 2.50/0.99      | m1_orders_2(sK3,X0,sK3) = iProver_top
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2108,plain,
% 2.50/0.99      ( sK3 != sK3
% 2.50/0.99      | sK3 != sK2
% 2.50/0.99      | sK0 != sK0
% 2.50/0.99      | m1_orders_2(sK3,sK0,sK3) = iProver_top
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_2106]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_14,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_11,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_154,plain,
% 2.50/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.50/0.99      | ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_14,c_11]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_155,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_154]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_761,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | sK0 != X1
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_155,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_762,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | ~ m1_orders_2(X1,sK0,X0)
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | v2_struct_0(sK0)
% 2.50/0.99      | ~ v3_orders_2(sK0)
% 2.50/0.99      | ~ v4_orders_2(sK0)
% 2.50/0.99      | ~ v5_orders_2(sK0)
% 2.50/0.99      | k1_xboole_0 = X0 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_761]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_766,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 2.50/0.99      | ~ m1_orders_2(X1,sK0,X0)
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | k1_xboole_0 = X0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_762,c_27,c_26,c_25,c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1700,plain,
% 2.50/0.99      ( ~ m1_orders_2(X0,sK0,sK3)
% 2.50/0.99      | ~ m1_orders_2(sK3,sK0,X0)
% 2.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | k1_xboole_0 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_766]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2839,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK3,sK0,sK3)
% 2.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | k1_xboole_0 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2842,plain,
% 2.50/0.99      ( k1_xboole_0 = sK3
% 2.50/0.99      | m1_orders_2(sK3,sK0,sK3) != iProver_top
% 2.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1481,plain,
% 2.50/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_6,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1480,plain,
% 2.50/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2232,plain,
% 2.50/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1481,c_1480]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10,plain,
% 2.50/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1477,plain,
% 2.50/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2992,plain,
% 2.50/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2232,c_1477]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_8,plain,
% 2.50/0.99      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_15,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.50/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ r1_xboole_0(X0,X3)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_529,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.50/0.99      | ~ r1_xboole_0(X0,X3)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK1 != X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_530,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | ~ r1_xboole_0(X2,X0)
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_613,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | X2 != X3
% 2.50/0.99      | X0 != X5
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_530]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_614,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | ~ l1_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_613]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_656,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 2.50/0.99      | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
% 2.50/0.99      | v2_struct_0(X1)
% 2.50/0.99      | ~ v3_orders_2(X1)
% 2.50/0.99      | ~ v4_orders_2(X1)
% 2.50/0.99      | ~ v5_orders_2(X1)
% 2.50/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.50/0.99      | sK0 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_614,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_657,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
% 2.50/0.99      | v2_struct_0(sK0)
% 2.50/0.99      | ~ v3_orders_2(sK0)
% 2.50/0.99      | ~ v4_orders_2(sK0)
% 2.50/0.99      | ~ v5_orders_2(sK0)
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_656]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_661,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
% 2.50/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_657,c_27,c_26,c_25,c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_888,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 2.50/0.99      | ~ r1_tarski(X1,k4_xboole_0(X2,X0)) ),
% 2.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_661]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1465,plain,
% 2.50/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.50/0.99      | r1_tarski(X1,k4_xboole_0(X2,X0)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3019,plain,
% 2.50/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2992,c_1465]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2752,plain,
% 2.50/0.99      ( sK3 = X0
% 2.50/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.50/0.99      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1476,c_1467]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3072,plain,
% 2.50/0.99      ( sK3 = sK2
% 2.50/0.99      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1475,c_2752]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_34,plain,
% 2.50/0.99      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2,plain,
% 2.50/0.99      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_19,negated_conjecture,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_212,plain,
% 2.50/0.99      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.50/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_213,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_212]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_421,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(X0,X1) | sK3 != X1 | sK2 != X0 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_213]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_422,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_423,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.50/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1,plain,
% 2.50/0.99      ( ~ r2_xboole_0(X0,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_431,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_213]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_432,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_433,plain,
% 2.50/0.99      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1616,plain,
% 2.50/0.99      ( ~ m2_orders_2(sK2,sK0,sK1)
% 2.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_884]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1617,plain,
% 2.50/0.99      ( m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1787,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | m1_orders_2(X0,sK0,sK3)
% 2.50/0.99      | m1_orders_2(sK3,sK0,X0)
% 2.50/0.99      | X0 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_880]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2041,plain,
% 2.50/0.99      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.50/0.99      | m1_orders_2(sK3,sK0,sK2)
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3)
% 2.50/0.99      | sK2 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1787]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2042,plain,
% 2.50/0.99      ( sK2 = sK3
% 2.50/0.99      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.50/0.99      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.50/0.99      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1797,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2081,plain,
% 2.50/0.99      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1797]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2082,plain,
% 2.50/0.99      ( sK2 = sK3
% 2.50/0.99      | r1_tarski(sK3,sK2) != iProver_top
% 2.50/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2534,plain,
% 2.50/0.99      ( ~ m1_orders_2(sK3,sK0,sK2)
% 2.50/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.50/0.99      | r1_tarski(sK3,sK2) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_788]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2535,plain,
% 2.50/0.99      ( m1_orders_2(sK3,sK0,sK2) != iProver_top
% 2.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.50/0.99      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2534]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3081,plain,
% 2.50/0.99      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_3072,c_34,c_35,c_423,c_433,c_1617,c_2042,c_2082,c_2535]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1033,plain,
% 2.50/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.50/0.99      | m2_orders_2(X3,X4,X5)
% 2.50/0.99      | X3 != X0
% 2.50/0.99      | X4 != X1
% 2.50/0.99      | X5 != X2 ),
% 2.50/0.99      theory(equality) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1641,plain,
% 2.50/0.99      ( m2_orders_2(X0,X1,X2)
% 2.50/0.99      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | X2 != sK1
% 2.50/0.99      | X0 != sK3
% 2.50/0.99      | X1 != sK0 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1033]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1687,plain,
% 2.50/0.99      ( m2_orders_2(X0,X1,sK1)
% 2.50/0.99      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | X0 != sK3
% 2.50/0.99      | X1 != sK0
% 2.50/0.99      | sK1 != sK1 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1641]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3110,plain,
% 2.50/0.99      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.50/0.99      | m2_orders_2(k1_xboole_0,X0,sK1)
% 2.50/0.99      | X0 != sK0
% 2.50/0.99      | sK1 != sK1
% 2.50/0.99      | k1_xboole_0 != sK3 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1687]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3111,plain,
% 2.50/0.99      ( X0 != sK0
% 2.50/0.99      | sK1 != sK1
% 2.50/0.99      | k1_xboole_0 != sK3
% 2.50/0.99      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(k1_xboole_0,X0,sK1) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3110]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3113,plain,
% 2.50/0.99      ( sK1 != sK1
% 2.50/0.99      | sK0 != sK0
% 2.50/0.99      | k1_xboole_0 != sK3
% 2.50/0.99      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.50/0.99      | m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3111]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3143,plain,
% 2.50/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2753,c_34,c_35,c_73,c_77,c_410,c_423,c_433,c_1614,c_1617,
% 2.50/0.99                 c_1630,c_1688,c_1803,c_2042,c_2082,c_2108,c_2535,c_2842,
% 2.50/0.99                 c_3019,c_3113]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3150,plain,
% 2.50/0.99      ( $false ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1476,c_3143]) ).
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  ------                               Statistics
% 2.50/0.99  
% 2.50/0.99  ------ General
% 2.50/0.99  
% 2.50/0.99  abstr_ref_over_cycles:                  0
% 2.50/0.99  abstr_ref_under_cycles:                 0
% 2.50/0.99  gc_basic_clause_elim:                   0
% 2.50/0.99  forced_gc_time:                         0
% 2.50/0.99  parsing_time:                           0.011
% 2.50/0.99  unif_index_cands_time:                  0.
% 2.50/0.99  unif_index_add_time:                    0.
% 2.50/0.99  orderings_time:                         0.
% 2.50/0.99  out_proof_time:                         0.016
% 2.50/0.99  total_time:                             0.128
% 2.50/0.99  num_of_symbols:                         52
% 2.50/0.99  num_of_terms:                           2145
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing
% 2.50/0.99  
% 2.50/0.99  num_of_splits:                          0
% 2.50/0.99  num_of_split_atoms:                     0
% 2.50/0.99  num_of_reused_defs:                     0
% 2.50/0.99  num_eq_ax_congr_red:                    11
% 2.50/0.99  num_of_sem_filtered_clauses:            1
% 2.50/0.99  num_of_subtypes:                        0
% 2.50/0.99  monotx_restored_types:                  0
% 2.50/0.99  sat_num_of_epr_types:                   0
% 2.50/0.99  sat_num_of_non_cyclic_types:            0
% 2.50/0.99  sat_guarded_non_collapsed_types:        0
% 2.50/0.99  num_pure_diseq_elim:                    0
% 2.50/0.99  simp_replaced_by:                       0
% 2.50/0.99  res_preprocessed:                       98
% 2.50/0.99  prep_upred:                             0
% 2.50/0.99  prep_unflattend:                        22
% 2.50/0.99  smt_new_axioms:                         0
% 2.50/0.99  pred_elim_cands:                        4
% 2.50/0.99  pred_elim:                              8
% 2.50/0.99  pred_elim_cl:                           9
% 2.50/0.99  pred_elim_cycles:                       11
% 2.50/0.99  merged_defs:                            10
% 2.50/0.99  merged_defs_ncl:                        0
% 2.50/0.99  bin_hyper_res:                          10
% 2.50/0.99  prep_cycles:                            4
% 2.50/0.99  pred_elim_time:                         0.011
% 2.50/0.99  splitting_time:                         0.
% 2.50/0.99  sem_filter_time:                        0.
% 2.50/0.99  monotx_time:                            0.
% 2.50/0.99  subtype_inf_time:                       0.
% 2.50/0.99  
% 2.50/0.99  ------ Problem properties
% 2.50/0.99  
% 2.50/0.99  clauses:                                18
% 2.50/0.99  conjectures:                            2
% 2.50/0.99  epr:                                    9
% 2.50/0.99  horn:                                   16
% 2.50/0.99  ground:                                 5
% 2.50/0.99  unary:                                  4
% 2.50/0.99  binary:                                 6
% 2.50/0.99  lits:                                   45
% 2.50/0.99  lits_eq:                                8
% 2.50/0.99  fd_pure:                                0
% 2.50/0.99  fd_pseudo:                              0
% 2.50/0.99  fd_cond:                                1
% 2.50/0.99  fd_pseudo_cond:                         3
% 2.50/0.99  ac_symbols:                             0
% 2.50/0.99  
% 2.50/0.99  ------ Propositional Solver
% 2.50/0.99  
% 2.50/0.99  prop_solver_calls:                      28
% 2.50/0.99  prop_fast_solver_calls:                 797
% 2.50/0.99  smt_solver_calls:                       0
% 2.50/0.99  smt_fast_solver_calls:                  0
% 2.50/0.99  prop_num_of_clauses:                    1058
% 2.50/0.99  prop_preprocess_simplified:             3650
% 2.50/0.99  prop_fo_subsumed:                       34
% 2.50/0.99  prop_solver_time:                       0.
% 2.50/0.99  smt_solver_time:                        0.
% 2.50/0.99  smt_fast_solver_time:                   0.
% 2.50/0.99  prop_fast_solver_time:                  0.
% 2.50/0.99  prop_unsat_core_time:                   0.
% 2.50/0.99  
% 2.50/0.99  ------ QBF
% 2.50/0.99  
% 2.50/0.99  qbf_q_res:                              0
% 2.50/0.99  qbf_num_tautologies:                    0
% 2.50/0.99  qbf_prep_cycles:                        0
% 2.50/0.99  
% 2.50/0.99  ------ BMC1
% 2.50/0.99  
% 2.50/0.99  bmc1_current_bound:                     -1
% 2.50/0.99  bmc1_last_solved_bound:                 -1
% 2.50/0.99  bmc1_unsat_core_size:                   -1
% 2.50/0.99  bmc1_unsat_core_parents_size:           -1
% 2.50/0.99  bmc1_merge_next_fun:                    0
% 2.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation
% 2.50/0.99  
% 2.50/0.99  inst_num_of_clauses:                    253
% 2.50/0.99  inst_num_in_passive:                    105
% 2.50/0.99  inst_num_in_active:                     145
% 2.50/0.99  inst_num_in_unprocessed:                3
% 2.50/0.99  inst_num_of_loops:                      150
% 2.50/0.99  inst_num_of_learning_restarts:          0
% 2.50/0.99  inst_num_moves_active_passive:          2
% 2.50/0.99  inst_lit_activity:                      0
% 2.50/0.99  inst_lit_activity_moves:                0
% 2.50/0.99  inst_num_tautologies:                   0
% 2.50/0.99  inst_num_prop_implied:                  0
% 2.50/0.99  inst_num_existing_simplified:           0
% 2.50/0.99  inst_num_eq_res_simplified:             0
% 2.50/0.99  inst_num_child_elim:                    0
% 2.50/0.99  inst_num_of_dismatching_blockings:      13
% 2.50/0.99  inst_num_of_non_proper_insts:           228
% 2.50/0.99  inst_num_of_duplicates:                 0
% 2.50/0.99  inst_inst_num_from_inst_to_res:         0
% 2.50/0.99  inst_dismatching_checking_time:         0.
% 2.50/0.99  
% 2.50/0.99  ------ Resolution
% 2.50/0.99  
% 2.50/0.99  res_num_of_clauses:                     0
% 2.50/0.99  res_num_in_passive:                     0
% 2.50/0.99  res_num_in_active:                      0
% 2.50/0.99  res_num_of_loops:                       102
% 2.50/0.99  res_forward_subset_subsumed:            21
% 2.50/0.99  res_backward_subset_subsumed:           0
% 2.50/0.99  res_forward_subsumed:                   0
% 2.50/0.99  res_backward_subsumed:                  0
% 2.50/0.99  res_forward_subsumption_resolution:     0
% 2.50/0.99  res_backward_subsumption_resolution:    0
% 2.50/0.99  res_clause_to_clause_subsumption:       128
% 2.50/0.99  res_orphan_elimination:                 0
% 2.50/0.99  res_tautology_del:                      37
% 2.50/0.99  res_num_eq_res_simplified:              4
% 2.50/0.99  res_num_sel_changes:                    0
% 2.50/0.99  res_moves_from_active_to_pass:          0
% 2.50/0.99  
% 2.50/0.99  ------ Superposition
% 2.50/0.99  
% 2.50/0.99  sup_time_total:                         0.
% 2.50/0.99  sup_time_generating:                    0.
% 2.50/0.99  sup_time_sim_full:                      0.
% 2.50/0.99  sup_time_sim_immed:                     0.
% 2.50/0.99  
% 2.50/0.99  sup_num_of_clauses:                     40
% 2.50/0.99  sup_num_in_active:                      25
% 2.50/0.99  sup_num_in_passive:                     15
% 2.50/0.99  sup_num_of_loops:                       28
% 2.50/0.99  sup_fw_superposition:                   14
% 2.50/0.99  sup_bw_superposition:                   24
% 2.50/0.99  sup_immediate_simplified:               2
% 2.50/0.99  sup_given_eliminated:                   0
% 2.50/0.99  comparisons_done:                       0
% 2.50/0.99  comparisons_avoided:                    0
% 2.50/0.99  
% 2.50/0.99  ------ Simplifications
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  sim_fw_subset_subsumed:                 2
% 2.50/0.99  sim_bw_subset_subsumed:                 9
% 2.50/0.99  sim_fw_subsumed:                        0
% 2.50/0.99  sim_bw_subsumed:                        0
% 2.50/0.99  sim_fw_subsumption_res:                 0
% 2.50/0.99  sim_bw_subsumption_res:                 0
% 2.50/0.99  sim_tautology_del:                      0
% 2.50/0.99  sim_eq_tautology_del:                   2
% 2.50/0.99  sim_eq_res_simp:                        0
% 2.50/0.99  sim_fw_demodulated:                     0
% 2.50/0.99  sim_bw_demodulated:                     0
% 2.50/0.99  sim_light_normalised:                   0
% 2.50/0.99  sim_joinable_taut:                      0
% 2.50/0.99  sim_joinable_simp:                      0
% 2.50/0.99  sim_ac_normalised:                      0
% 2.50/0.99  sim_smt_subsumption:                    0
% 2.50/0.99  
%------------------------------------------------------------------------------
