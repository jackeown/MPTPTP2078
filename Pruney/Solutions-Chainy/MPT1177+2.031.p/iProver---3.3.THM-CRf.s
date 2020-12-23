%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:53 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  176 (7312 expanded)
%              Number of clauses        :  110 (1362 expanded)
%              Number of leaves         :   15 (2375 expanded)
%              Depth                    :   30
%              Number of atoms          :  880 (70419 expanded)
%              Number of equality atoms :  175 (1726 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).

fof(f66,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f21])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1402,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_195,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_196,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_406,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_196])).

cnf(c_407,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1395,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_396,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_196])).

cnf(c_397,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_398,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_408,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1845,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2158,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_2159,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1398,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1399,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_465,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_466,plain,
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
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_676,plain,
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
    inference(resolution_lifted,[status(thm)],[c_466,c_21])).

cnf(c_677,plain,
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
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_681,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_25,c_24,c_23,c_22])).

cnf(c_853,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_681])).

cnf(c_1390,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_2483,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1390])).

cnf(c_2553,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_2483])).

cnf(c_32,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_33,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1846,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_2315,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_2316,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_2595,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2553,c_32,c_33,c_408,c_2316])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_537,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_538,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_655,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_538,c_21])).

cnf(c_656,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_660,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_25,c_24,c_23,c_22])).

cnf(c_857,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_660])).

cnf(c_1389,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_760,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_761,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_763,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_25,c_24,c_23,c_22])).

cnf(c_1393,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1670,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1393])).

cnf(c_1789,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1670])).

cnf(c_2605,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2595,c_1789])).

cnf(c_3048,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_398,c_408,c_2159,c_2605])).

cnf(c_1788,plain,
    ( m1_orders_2(X0,sK0,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1670])).

cnf(c_3061,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_1788])).

cnf(c_1403,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3099,plain,
    ( sK3 = sK2
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3061,c_1403])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_193,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_194,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_383,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_194])).

cnf(c_384,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_385,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1524,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_1525,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_1540,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1541,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_3217,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3099,c_33,c_385,c_398,c_408,c_1525,c_1541,c_2159,c_2605])).

cnf(c_3226,plain,
    ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3217,c_2595])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_9])).

cnf(c_143,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_736,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_21])).

cnf(c_737,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_741,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_25,c_24,c_23,c_22])).

cnf(c_742,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_741])).

cnf(c_1394,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1668,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1394])).

cnf(c_2705,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1668])).

cnf(c_3347,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3226,c_2705])).

cnf(c_3351,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3347,c_3226])).

cnf(c_3376,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3351,c_1398])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1401,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1981,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1402,c_1401])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_504,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_505,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_588,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X3,X4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 != X3
    | k4_xboole_0(X5,X4) != X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_505])).

cnf(c_589,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(k4_xboole_0(X2,X3),X1,sK1)
    | ~ r1_tarski(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_631,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(k4_xboole_0(X2,X3),X1,sK1)
    | ~ r1_tarski(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_589,c_21])).

cnf(c_632,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
    | ~ r1_tarski(X0,X2)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
    | ~ r1_tarski(X0,X2)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_25,c_24,c_23,c_22])).

cnf(c_861,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
    | ~ r1_tarski(X0,X2) ),
    inference(equality_resolution_simp,[status(thm)],[c_636])).

cnf(c_1388,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_2537,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_1388])).

cnf(c_3907,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2537,c_3376])).

cnf(c_3915,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_3907])).

cnf(c_3921,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1402,c_3915])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:44:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.86/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.86/0.98  
% 1.86/0.98  ------  iProver source info
% 1.86/0.98  
% 1.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.86/0.98  git: non_committed_changes: false
% 1.86/0.98  git: last_make_outside_of_git: false
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options
% 1.86/0.98  
% 1.86/0.98  --out_options                           all
% 1.86/0.98  --tptp_safe_out                         true
% 1.86/0.98  --problem_path                          ""
% 1.86/0.98  --include_path                          ""
% 1.86/0.98  --clausifier                            res/vclausify_rel
% 1.86/0.98  --clausifier_options                    --mode clausify
% 1.86/0.98  --stdin                                 false
% 1.86/0.98  --stats_out                             all
% 1.86/0.98  
% 1.86/0.98  ------ General Options
% 1.86/0.98  
% 1.86/0.98  --fof                                   false
% 1.86/0.98  --time_out_real                         305.
% 1.86/0.98  --time_out_virtual                      -1.
% 1.86/0.98  --symbol_type_check                     false
% 1.86/0.98  --clausify_out                          false
% 1.86/0.98  --sig_cnt_out                           false
% 1.86/0.98  --trig_cnt_out                          false
% 1.86/0.98  --trig_cnt_out_tolerance                1.
% 1.86/0.98  --trig_cnt_out_sk_spl                   false
% 1.86/0.98  --abstr_cl_out                          false
% 1.86/0.98  
% 1.86/0.98  ------ Global Options
% 1.86/0.98  
% 1.86/0.98  --schedule                              default
% 1.86/0.98  --add_important_lit                     false
% 1.86/0.98  --prop_solver_per_cl                    1000
% 1.86/0.98  --min_unsat_core                        false
% 1.86/0.98  --soft_assumptions                      false
% 1.86/0.98  --soft_lemma_size                       3
% 1.86/0.98  --prop_impl_unit_size                   0
% 1.86/0.98  --prop_impl_unit                        []
% 1.86/0.98  --share_sel_clauses                     true
% 1.86/0.98  --reset_solvers                         false
% 1.86/0.98  --bc_imp_inh                            [conj_cone]
% 1.86/0.98  --conj_cone_tolerance                   3.
% 1.86/0.98  --extra_neg_conj                        none
% 1.86/0.98  --large_theory_mode                     true
% 1.86/0.98  --prolific_symb_bound                   200
% 1.86/0.98  --lt_threshold                          2000
% 1.86/0.98  --clause_weak_htbl                      true
% 1.86/0.98  --gc_record_bc_elim                     false
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing Options
% 1.86/0.98  
% 1.86/0.98  --preprocessing_flag                    true
% 1.86/0.98  --time_out_prep_mult                    0.1
% 1.86/0.98  --splitting_mode                        input
% 1.86/0.98  --splitting_grd                         true
% 1.86/0.98  --splitting_cvd                         false
% 1.86/0.98  --splitting_cvd_svl                     false
% 1.86/0.98  --splitting_nvd                         32
% 1.86/0.98  --sub_typing                            true
% 1.86/0.98  --prep_gs_sim                           true
% 1.86/0.98  --prep_unflatten                        true
% 1.86/0.98  --prep_res_sim                          true
% 1.86/0.98  --prep_upred                            true
% 1.86/0.98  --prep_sem_filter                       exhaustive
% 1.86/0.98  --prep_sem_filter_out                   false
% 1.86/0.98  --pred_elim                             true
% 1.86/0.98  --res_sim_input                         true
% 1.86/0.98  --eq_ax_congr_red                       true
% 1.86/0.98  --pure_diseq_elim                       true
% 1.86/0.98  --brand_transform                       false
% 1.86/0.98  --non_eq_to_eq                          false
% 1.86/0.98  --prep_def_merge                        true
% 1.86/0.98  --prep_def_merge_prop_impl              false
% 1.86/0.98  --prep_def_merge_mbd                    true
% 1.86/0.98  --prep_def_merge_tr_red                 false
% 1.86/0.98  --prep_def_merge_tr_cl                  false
% 1.86/0.98  --smt_preprocessing                     true
% 1.86/0.98  --smt_ac_axioms                         fast
% 1.86/0.98  --preprocessed_out                      false
% 1.86/0.98  --preprocessed_stats                    false
% 1.86/0.98  
% 1.86/0.98  ------ Abstraction refinement Options
% 1.86/0.98  
% 1.86/0.98  --abstr_ref                             []
% 1.86/0.98  --abstr_ref_prep                        false
% 1.86/0.98  --abstr_ref_until_sat                   false
% 1.86/0.98  --abstr_ref_sig_restrict                funpre
% 1.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.98  --abstr_ref_under                       []
% 1.86/0.98  
% 1.86/0.98  ------ SAT Options
% 1.86/0.98  
% 1.86/0.98  --sat_mode                              false
% 1.86/0.98  --sat_fm_restart_options                ""
% 1.86/0.98  --sat_gr_def                            false
% 1.86/0.98  --sat_epr_types                         true
% 1.86/0.98  --sat_non_cyclic_types                  false
% 1.86/0.98  --sat_finite_models                     false
% 1.86/0.98  --sat_fm_lemmas                         false
% 1.86/0.98  --sat_fm_prep                           false
% 1.86/0.98  --sat_fm_uc_incr                        true
% 1.86/0.98  --sat_out_model                         small
% 1.86/0.98  --sat_out_clauses                       false
% 1.86/0.98  
% 1.86/0.98  ------ QBF Options
% 1.86/0.98  
% 1.86/0.98  --qbf_mode                              false
% 1.86/0.98  --qbf_elim_univ                         false
% 1.86/0.98  --qbf_dom_inst                          none
% 1.86/0.98  --qbf_dom_pre_inst                      false
% 1.86/0.98  --qbf_sk_in                             false
% 1.86/0.98  --qbf_pred_elim                         true
% 1.86/0.98  --qbf_split                             512
% 1.86/0.98  
% 1.86/0.98  ------ BMC1 Options
% 1.86/0.98  
% 1.86/0.98  --bmc1_incremental                      false
% 1.86/0.98  --bmc1_axioms                           reachable_all
% 1.86/0.98  --bmc1_min_bound                        0
% 1.86/0.98  --bmc1_max_bound                        -1
% 1.86/0.98  --bmc1_max_bound_default                -1
% 1.86/0.98  --bmc1_symbol_reachability              true
% 1.86/0.98  --bmc1_property_lemmas                  false
% 1.86/0.98  --bmc1_k_induction                      false
% 1.86/0.98  --bmc1_non_equiv_states                 false
% 1.86/0.98  --bmc1_deadlock                         false
% 1.86/0.98  --bmc1_ucm                              false
% 1.86/0.98  --bmc1_add_unsat_core                   none
% 1.86/0.98  --bmc1_unsat_core_children              false
% 1.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.98  --bmc1_out_stat                         full
% 1.86/0.98  --bmc1_ground_init                      false
% 1.86/0.98  --bmc1_pre_inst_next_state              false
% 1.86/0.98  --bmc1_pre_inst_state                   false
% 1.86/0.98  --bmc1_pre_inst_reach_state             false
% 1.86/0.98  --bmc1_out_unsat_core                   false
% 1.86/0.98  --bmc1_aig_witness_out                  false
% 1.86/0.98  --bmc1_verbose                          false
% 1.86/0.98  --bmc1_dump_clauses_tptp                false
% 1.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.98  --bmc1_dump_file                        -
% 1.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.98  --bmc1_ucm_extend_mode                  1
% 1.86/0.98  --bmc1_ucm_init_mode                    2
% 1.86/0.98  --bmc1_ucm_cone_mode                    none
% 1.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.98  --bmc1_ucm_relax_model                  4
% 1.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.98  --bmc1_ucm_layered_model                none
% 1.86/0.99  --bmc1_ucm_max_lemma_size               10
% 1.86/0.99  
% 1.86/0.99  ------ AIG Options
% 1.86/0.99  
% 1.86/0.99  --aig_mode                              false
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation Options
% 1.86/0.99  
% 1.86/0.99  --instantiation_flag                    true
% 1.86/0.99  --inst_sos_flag                         false
% 1.86/0.99  --inst_sos_phase                        true
% 1.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel_side                     num_symb
% 1.86/0.99  --inst_solver_per_active                1400
% 1.86/0.99  --inst_solver_calls_frac                1.
% 1.86/0.99  --inst_passive_queue_type               priority_queues
% 1.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.99  --inst_passive_queues_freq              [25;2]
% 1.86/0.99  --inst_dismatching                      true
% 1.86/0.99  --inst_eager_unprocessed_to_passive     true
% 1.86/0.99  --inst_prop_sim_given                   true
% 1.86/0.99  --inst_prop_sim_new                     false
% 1.86/0.99  --inst_subs_new                         false
% 1.86/0.99  --inst_eq_res_simp                      false
% 1.86/0.99  --inst_subs_given                       false
% 1.86/0.99  --inst_orphan_elimination               true
% 1.86/0.99  --inst_learning_loop_flag               true
% 1.86/0.99  --inst_learning_start                   3000
% 1.86/0.99  --inst_learning_factor                  2
% 1.86/0.99  --inst_start_prop_sim_after_learn       3
% 1.86/0.99  --inst_sel_renew                        solver
% 1.86/0.99  --inst_lit_activity_flag                true
% 1.86/0.99  --inst_restr_to_given                   false
% 1.86/0.99  --inst_activity_threshold               500
% 1.86/0.99  --inst_out_proof                        true
% 1.86/0.99  
% 1.86/0.99  ------ Resolution Options
% 1.86/0.99  
% 1.86/0.99  --resolution_flag                       true
% 1.86/0.99  --res_lit_sel                           adaptive
% 1.86/0.99  --res_lit_sel_side                      none
% 1.86/0.99  --res_ordering                          kbo
% 1.86/0.99  --res_to_prop_solver                    active
% 1.86/0.99  --res_prop_simpl_new                    false
% 1.86/0.99  --res_prop_simpl_given                  true
% 1.86/0.99  --res_passive_queue_type                priority_queues
% 1.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.99  --res_passive_queues_freq               [15;5]
% 1.86/0.99  --res_forward_subs                      full
% 1.86/0.99  --res_backward_subs                     full
% 1.86/0.99  --res_forward_subs_resolution           true
% 1.86/0.99  --res_backward_subs_resolution          true
% 1.86/0.99  --res_orphan_elimination                true
% 1.86/0.99  --res_time_limit                        2.
% 1.86/0.99  --res_out_proof                         true
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Options
% 1.86/0.99  
% 1.86/0.99  --superposition_flag                    true
% 1.86/0.99  --sup_passive_queue_type                priority_queues
% 1.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.99  --demod_completeness_check              fast
% 1.86/0.99  --demod_use_ground                      true
% 1.86/0.99  --sup_to_prop_solver                    passive
% 1.86/0.99  --sup_prop_simpl_new                    true
% 1.86/0.99  --sup_prop_simpl_given                  true
% 1.86/0.99  --sup_fun_splitting                     false
% 1.86/0.99  --sup_smt_interval                      50000
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Simplification Setup
% 1.86/0.99  
% 1.86/0.99  --sup_indices_passive                   []
% 1.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_full_bw                           [BwDemod]
% 1.86/0.99  --sup_immed_triv                        [TrivRules]
% 1.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_immed_bw_main                     []
% 1.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  
% 1.86/0.99  ------ Combination Options
% 1.86/0.99  
% 1.86/0.99  --comb_res_mult                         3
% 1.86/0.99  --comb_sup_mult                         2
% 1.86/0.99  --comb_inst_mult                        10
% 1.86/0.99  
% 1.86/0.99  ------ Debug Options
% 1.86/0.99  
% 1.86/0.99  --dbg_backtrace                         false
% 1.86/0.99  --dbg_dump_prop_clauses                 false
% 1.86/0.99  --dbg_dump_prop_clauses_file            -
% 1.86/0.99  --dbg_out_stat                          false
% 1.86/0.99  ------ Parsing...
% 1.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.86/0.99  ------ Proving...
% 1.86/0.99  ------ Problem Properties 
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  clauses                                 16
% 1.86/0.99  conjectures                             2
% 1.86/0.99  EPR                                     9
% 1.86/0.99  Horn                                    14
% 1.86/0.99  unary                                   3
% 1.86/0.99  binary                                  5
% 1.86/0.99  lits                                    42
% 1.86/0.99  lits eq                                 8
% 1.86/0.99  fd_pure                                 0
% 1.86/0.99  fd_pseudo                               0
% 1.86/0.99  fd_cond                                 1
% 1.86/0.99  fd_pseudo_cond                          3
% 1.86/0.99  AC symbols                              0
% 1.86/0.99  
% 1.86/0.99  ------ Schedule dynamic 5 is on 
% 1.86/0.99  
% 1.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  ------ 
% 1.86/0.99  Current options:
% 1.86/0.99  ------ 
% 1.86/0.99  
% 1.86/0.99  ------ Input Options
% 1.86/0.99  
% 1.86/0.99  --out_options                           all
% 1.86/0.99  --tptp_safe_out                         true
% 1.86/0.99  --problem_path                          ""
% 1.86/0.99  --include_path                          ""
% 1.86/0.99  --clausifier                            res/vclausify_rel
% 1.86/0.99  --clausifier_options                    --mode clausify
% 1.86/0.99  --stdin                                 false
% 1.86/0.99  --stats_out                             all
% 1.86/0.99  
% 1.86/0.99  ------ General Options
% 1.86/0.99  
% 1.86/0.99  --fof                                   false
% 1.86/0.99  --time_out_real                         305.
% 1.86/0.99  --time_out_virtual                      -1.
% 1.86/0.99  --symbol_type_check                     false
% 1.86/0.99  --clausify_out                          false
% 1.86/0.99  --sig_cnt_out                           false
% 1.86/0.99  --trig_cnt_out                          false
% 1.86/0.99  --trig_cnt_out_tolerance                1.
% 1.86/0.99  --trig_cnt_out_sk_spl                   false
% 1.86/0.99  --abstr_cl_out                          false
% 1.86/0.99  
% 1.86/0.99  ------ Global Options
% 1.86/0.99  
% 1.86/0.99  --schedule                              default
% 1.86/0.99  --add_important_lit                     false
% 1.86/0.99  --prop_solver_per_cl                    1000
% 1.86/0.99  --min_unsat_core                        false
% 1.86/0.99  --soft_assumptions                      false
% 1.86/0.99  --soft_lemma_size                       3
% 1.86/0.99  --prop_impl_unit_size                   0
% 1.86/0.99  --prop_impl_unit                        []
% 1.86/0.99  --share_sel_clauses                     true
% 1.86/0.99  --reset_solvers                         false
% 1.86/0.99  --bc_imp_inh                            [conj_cone]
% 1.86/0.99  --conj_cone_tolerance                   3.
% 1.86/0.99  --extra_neg_conj                        none
% 1.86/0.99  --large_theory_mode                     true
% 1.86/0.99  --prolific_symb_bound                   200
% 1.86/0.99  --lt_threshold                          2000
% 1.86/0.99  --clause_weak_htbl                      true
% 1.86/0.99  --gc_record_bc_elim                     false
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing Options
% 1.86/0.99  
% 1.86/0.99  --preprocessing_flag                    true
% 1.86/0.99  --time_out_prep_mult                    0.1
% 1.86/0.99  --splitting_mode                        input
% 1.86/0.99  --splitting_grd                         true
% 1.86/0.99  --splitting_cvd                         false
% 1.86/0.99  --splitting_cvd_svl                     false
% 1.86/0.99  --splitting_nvd                         32
% 1.86/0.99  --sub_typing                            true
% 1.86/0.99  --prep_gs_sim                           true
% 1.86/0.99  --prep_unflatten                        true
% 1.86/0.99  --prep_res_sim                          true
% 1.86/0.99  --prep_upred                            true
% 1.86/0.99  --prep_sem_filter                       exhaustive
% 1.86/0.99  --prep_sem_filter_out                   false
% 1.86/0.99  --pred_elim                             true
% 1.86/0.99  --res_sim_input                         true
% 1.86/0.99  --eq_ax_congr_red                       true
% 1.86/0.99  --pure_diseq_elim                       true
% 1.86/0.99  --brand_transform                       false
% 1.86/0.99  --non_eq_to_eq                          false
% 1.86/0.99  --prep_def_merge                        true
% 1.86/0.99  --prep_def_merge_prop_impl              false
% 1.86/0.99  --prep_def_merge_mbd                    true
% 1.86/0.99  --prep_def_merge_tr_red                 false
% 1.86/0.99  --prep_def_merge_tr_cl                  false
% 1.86/0.99  --smt_preprocessing                     true
% 1.86/0.99  --smt_ac_axioms                         fast
% 1.86/0.99  --preprocessed_out                      false
% 1.86/0.99  --preprocessed_stats                    false
% 1.86/0.99  
% 1.86/0.99  ------ Abstraction refinement Options
% 1.86/0.99  
% 1.86/0.99  --abstr_ref                             []
% 1.86/0.99  --abstr_ref_prep                        false
% 1.86/0.99  --abstr_ref_until_sat                   false
% 1.86/0.99  --abstr_ref_sig_restrict                funpre
% 1.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.99  --abstr_ref_under                       []
% 1.86/0.99  
% 1.86/0.99  ------ SAT Options
% 1.86/0.99  
% 1.86/0.99  --sat_mode                              false
% 1.86/0.99  --sat_fm_restart_options                ""
% 1.86/0.99  --sat_gr_def                            false
% 1.86/0.99  --sat_epr_types                         true
% 1.86/0.99  --sat_non_cyclic_types                  false
% 1.86/0.99  --sat_finite_models                     false
% 1.86/0.99  --sat_fm_lemmas                         false
% 1.86/0.99  --sat_fm_prep                           false
% 1.86/0.99  --sat_fm_uc_incr                        true
% 1.86/0.99  --sat_out_model                         small
% 1.86/0.99  --sat_out_clauses                       false
% 1.86/0.99  
% 1.86/0.99  ------ QBF Options
% 1.86/0.99  
% 1.86/0.99  --qbf_mode                              false
% 1.86/0.99  --qbf_elim_univ                         false
% 1.86/0.99  --qbf_dom_inst                          none
% 1.86/0.99  --qbf_dom_pre_inst                      false
% 1.86/0.99  --qbf_sk_in                             false
% 1.86/0.99  --qbf_pred_elim                         true
% 1.86/0.99  --qbf_split                             512
% 1.86/0.99  
% 1.86/0.99  ------ BMC1 Options
% 1.86/0.99  
% 1.86/0.99  --bmc1_incremental                      false
% 1.86/0.99  --bmc1_axioms                           reachable_all
% 1.86/0.99  --bmc1_min_bound                        0
% 1.86/0.99  --bmc1_max_bound                        -1
% 1.86/0.99  --bmc1_max_bound_default                -1
% 1.86/0.99  --bmc1_symbol_reachability              true
% 1.86/0.99  --bmc1_property_lemmas                  false
% 1.86/0.99  --bmc1_k_induction                      false
% 1.86/0.99  --bmc1_non_equiv_states                 false
% 1.86/0.99  --bmc1_deadlock                         false
% 1.86/0.99  --bmc1_ucm                              false
% 1.86/0.99  --bmc1_add_unsat_core                   none
% 1.86/0.99  --bmc1_unsat_core_children              false
% 1.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.99  --bmc1_out_stat                         full
% 1.86/0.99  --bmc1_ground_init                      false
% 1.86/0.99  --bmc1_pre_inst_next_state              false
% 1.86/0.99  --bmc1_pre_inst_state                   false
% 1.86/0.99  --bmc1_pre_inst_reach_state             false
% 1.86/0.99  --bmc1_out_unsat_core                   false
% 1.86/0.99  --bmc1_aig_witness_out                  false
% 1.86/0.99  --bmc1_verbose                          false
% 1.86/0.99  --bmc1_dump_clauses_tptp                false
% 1.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.99  --bmc1_dump_file                        -
% 1.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.99  --bmc1_ucm_extend_mode                  1
% 1.86/0.99  --bmc1_ucm_init_mode                    2
% 1.86/0.99  --bmc1_ucm_cone_mode                    none
% 1.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.99  --bmc1_ucm_relax_model                  4
% 1.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.99  --bmc1_ucm_layered_model                none
% 1.86/0.99  --bmc1_ucm_max_lemma_size               10
% 1.86/0.99  
% 1.86/0.99  ------ AIG Options
% 1.86/0.99  
% 1.86/0.99  --aig_mode                              false
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation Options
% 1.86/0.99  
% 1.86/0.99  --instantiation_flag                    true
% 1.86/0.99  --inst_sos_flag                         false
% 1.86/0.99  --inst_sos_phase                        true
% 1.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel_side                     none
% 1.86/0.99  --inst_solver_per_active                1400
% 1.86/0.99  --inst_solver_calls_frac                1.
% 1.86/0.99  --inst_passive_queue_type               priority_queues
% 1.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.99  --inst_passive_queues_freq              [25;2]
% 1.86/0.99  --inst_dismatching                      true
% 1.86/0.99  --inst_eager_unprocessed_to_passive     true
% 1.86/0.99  --inst_prop_sim_given                   true
% 1.86/0.99  --inst_prop_sim_new                     false
% 1.86/0.99  --inst_subs_new                         false
% 1.86/0.99  --inst_eq_res_simp                      false
% 1.86/0.99  --inst_subs_given                       false
% 1.86/0.99  --inst_orphan_elimination               true
% 1.86/0.99  --inst_learning_loop_flag               true
% 1.86/0.99  --inst_learning_start                   3000
% 1.86/0.99  --inst_learning_factor                  2
% 1.86/0.99  --inst_start_prop_sim_after_learn       3
% 1.86/0.99  --inst_sel_renew                        solver
% 1.86/0.99  --inst_lit_activity_flag                true
% 1.86/0.99  --inst_restr_to_given                   false
% 1.86/0.99  --inst_activity_threshold               500
% 1.86/0.99  --inst_out_proof                        true
% 1.86/0.99  
% 1.86/0.99  ------ Resolution Options
% 1.86/0.99  
% 1.86/0.99  --resolution_flag                       false
% 1.86/0.99  --res_lit_sel                           adaptive
% 1.86/0.99  --res_lit_sel_side                      none
% 1.86/0.99  --res_ordering                          kbo
% 1.86/0.99  --res_to_prop_solver                    active
% 1.86/0.99  --res_prop_simpl_new                    false
% 1.86/0.99  --res_prop_simpl_given                  true
% 1.86/0.99  --res_passive_queue_type                priority_queues
% 1.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.99  --res_passive_queues_freq               [15;5]
% 1.86/0.99  --res_forward_subs                      full
% 1.86/0.99  --res_backward_subs                     full
% 1.86/0.99  --res_forward_subs_resolution           true
% 1.86/0.99  --res_backward_subs_resolution          true
% 1.86/0.99  --res_orphan_elimination                true
% 1.86/0.99  --res_time_limit                        2.
% 1.86/0.99  --res_out_proof                         true
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Options
% 1.86/0.99  
% 1.86/0.99  --superposition_flag                    true
% 1.86/0.99  --sup_passive_queue_type                priority_queues
% 1.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.99  --demod_completeness_check              fast
% 1.86/0.99  --demod_use_ground                      true
% 1.86/0.99  --sup_to_prop_solver                    passive
% 1.86/0.99  --sup_prop_simpl_new                    true
% 1.86/0.99  --sup_prop_simpl_given                  true
% 1.86/0.99  --sup_fun_splitting                     false
% 1.86/0.99  --sup_smt_interval                      50000
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Simplification Setup
% 1.86/0.99  
% 1.86/0.99  --sup_indices_passive                   []
% 1.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_full_bw                           [BwDemod]
% 1.86/0.99  --sup_immed_triv                        [TrivRules]
% 1.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_immed_bw_main                     []
% 1.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  
% 1.86/0.99  ------ Combination Options
% 1.86/0.99  
% 1.86/0.99  --comb_res_mult                         3
% 1.86/0.99  --comb_sup_mult                         2
% 1.86/0.99  --comb_inst_mult                        10
% 1.86/0.99  
% 1.86/0.99  ------ Debug Options
% 1.86/0.99  
% 1.86/0.99  --dbg_backtrace                         false
% 1.86/0.99  --dbg_dump_prop_clauses                 false
% 1.86/0.99  --dbg_dump_prop_clauses_file            -
% 1.86/0.99  --dbg_out_stat                          false
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  ------ Proving...
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS status Theorem for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99   Resolution empty clause
% 1.86/0.99  
% 1.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  fof(f2,axiom,(
% 1.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f31,plain,(
% 1.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.86/0.99    inference(nnf_transformation,[],[f2])).
% 1.86/0.99  
% 1.86/0.99  fof(f32,plain,(
% 1.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.86/0.99    inference(flattening,[],[f31])).
% 1.86/0.99  
% 1.86/0.99  fof(f45,plain,(
% 1.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.86/0.99    inference(cnf_transformation,[],[f32])).
% 1.86/0.99  
% 1.86/0.99  fof(f70,plain,(
% 1.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.86/0.99    inference(equality_resolution,[],[f45])).
% 1.86/0.99  
% 1.86/0.99  fof(f1,axiom,(
% 1.86/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f29,plain,(
% 1.86/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.86/0.99    inference(nnf_transformation,[],[f1])).
% 1.86/0.99  
% 1.86/0.99  fof(f30,plain,(
% 1.86/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.86/0.99    inference(flattening,[],[f29])).
% 1.86/0.99  
% 1.86/0.99  fof(f43,plain,(
% 1.86/0.99    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f68,plain,(
% 1.86/0.99    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.86/0.99    inference(equality_resolution,[],[f43])).
% 1.86/0.99  
% 1.86/0.99  fof(f11,conjecture,(
% 1.86/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f12,negated_conjecture,(
% 1.86/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.86/0.99    inference(negated_conjecture,[],[f11])).
% 1.86/0.99  
% 1.86/0.99  fof(f27,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f12])).
% 1.86/0.99  
% 1.86/0.99  fof(f28,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f27])).
% 1.86/0.99  
% 1.86/0.99  fof(f35,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.86/0.99    inference(nnf_transformation,[],[f28])).
% 1.86/0.99  
% 1.86/0.99  fof(f36,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f35])).
% 1.86/0.99  
% 1.86/0.99  fof(f40,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f39,plain,(
% 1.86/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f38,plain,(
% 1.86/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f37,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f41,plain,(
% 1.86/0.99    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).
% 1.86/0.99  
% 1.86/0.99  fof(f66,plain,(
% 1.86/0.99    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f42,plain,(
% 1.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f47,plain,(
% 1.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f32])).
% 1.86/0.99  
% 1.86/0.99  fof(f64,plain,(
% 1.86/0.99    m2_orders_2(sK2,sK0,sK1)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f65,plain,(
% 1.86/0.99    m2_orders_2(sK3,sK0,sK1)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f10,axiom,(
% 1.86/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f25,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f10])).
% 1.86/0.99  
% 1.86/0.99  fof(f26,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f25])).
% 1.86/0.99  
% 1.86/0.99  fof(f34,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(nnf_transformation,[],[f26])).
% 1.86/0.99  
% 1.86/0.99  fof(f57,plain,(
% 1.86/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f34])).
% 1.86/0.99  
% 1.86/0.99  fof(f63,plain,(
% 1.86/0.99    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f62,plain,(
% 1.86/0.99    l1_orders_2(sK0)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f58,plain,(
% 1.86/0.99    ~v2_struct_0(sK0)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f59,plain,(
% 1.86/0.99    v3_orders_2(sK0)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f60,plain,(
% 1.86/0.99    v4_orders_2(sK0)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f61,plain,(
% 1.86/0.99    v5_orders_2(sK0)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f6,axiom,(
% 1.86/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f13,plain,(
% 1.86/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.86/0.99  
% 1.86/0.99  fof(f17,plain,(
% 1.86/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f13])).
% 1.86/0.99  
% 1.86/0.99  fof(f18,plain,(
% 1.86/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f17])).
% 1.86/0.99  
% 1.86/0.99  fof(f52,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f18])).
% 1.86/0.99  
% 1.86/0.99  fof(f7,axiom,(
% 1.86/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f19,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f7])).
% 1.86/0.99  
% 1.86/0.99  fof(f20,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f19])).
% 1.86/0.99  
% 1.86/0.99  fof(f53,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f20])).
% 1.86/0.99  
% 1.86/0.99  fof(f44,plain,(
% 1.86/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f67,plain,(
% 1.86/0.99    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.86/0.99    inference(cnf_transformation,[],[f41])).
% 1.86/0.99  
% 1.86/0.99  fof(f8,axiom,(
% 1.86/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f21,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f8])).
% 1.86/0.99  
% 1.86/0.99  fof(f22,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f21])).
% 1.86/0.99  
% 1.86/0.99  fof(f54,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f22])).
% 1.86/0.99  
% 1.86/0.99  fof(f5,axiom,(
% 1.86/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f15,plain,(
% 1.86/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f5])).
% 1.86/0.99  
% 1.86/0.99  fof(f16,plain,(
% 1.86/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f15])).
% 1.86/0.99  
% 1.86/0.99  fof(f51,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f3,axiom,(
% 1.86/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f33,plain,(
% 1.86/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.86/0.99    inference(nnf_transformation,[],[f3])).
% 1.86/0.99  
% 1.86/0.99  fof(f49,plain,(
% 1.86/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f33])).
% 1.86/0.99  
% 1.86/0.99  fof(f4,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f14,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.86/0.99    inference(ennf_transformation,[],[f4])).
% 1.86/0.99  
% 1.86/0.99  fof(f50,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f14])).
% 1.86/0.99  
% 1.86/0.99  fof(f9,axiom,(
% 1.86/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f23,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f9])).
% 1.86/0.99  
% 1.86/0.99  fof(f24,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f23])).
% 1.86/0.99  
% 1.86/0.99  fof(f55,plain,(
% 1.86/0.99    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f24])).
% 1.86/0.99  
% 1.86/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f70]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1402,plain,
% 1.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1,plain,
% 1.86/0.99      ( ~ r2_xboole_0(X0,X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_17,negated_conjecture,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_195,plain,
% 1.86/0.99      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 1.86/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_196,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_195]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_406,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_196]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_407,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1395,plain,
% 1.86/0.99      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2,plain,
% 1.86/0.99      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_396,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(X0,X1) | sK3 != X1 | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_196]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_397,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_398,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 1.86/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_408,plain,
% 1.86/0.99      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3,plain,
% 1.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1845,plain,
% 1.86/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2158,plain,
% 1.86/0.99      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_1845]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2159,plain,
% 1.86/0.99      ( sK2 = sK3
% 1.86/0.99      | r1_tarski(sK3,sK2) != iProver_top
% 1.86/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_19,negated_conjecture,
% 1.86/0.99      ( m2_orders_2(sK2,sK0,sK1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1398,plain,
% 1.86/0.99      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_18,negated_conjecture,
% 1.86/0.99      ( m2_orders_2(sK3,sK0,sK1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1399,plain,
% 1.86/0.99      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_14,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m2_orders_2(X3,X1,X2)
% 1.86/0.99      | m1_orders_2(X3,X1,X0)
% 1.86/0.99      | m1_orders_2(X0,X1,X3)
% 1.86/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | X3 = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_20,negated_conjecture,
% 1.86/0.99      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 1.86/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_465,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m2_orders_2(X3,X1,X2)
% 1.86/0.99      | m1_orders_2(X3,X1,X0)
% 1.86/0.99      | m1_orders_2(X0,X1,X3)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | X3 = X0
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK1 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_466,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 1.86/0.99      | m1_orders_2(X0,X1,X2)
% 1.86/0.99      | m1_orders_2(X2,X1,X0)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | X0 = X2
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_21,negated_conjecture,
% 1.86/0.99      ( l1_orders_2(sK0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_676,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 1.86/0.99      | m1_orders_2(X0,X1,X2)
% 1.86/0.99      | m1_orders_2(X2,X1,X0)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | X2 = X0
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK0 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_466,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_677,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 1.86/0.99      | m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | v2_struct_0(sK0)
% 1.86/0.99      | ~ v3_orders_2(sK0)
% 1.86/0.99      | ~ v4_orders_2(sK0)
% 1.86/0.99      | ~ v5_orders_2(sK0)
% 1.86/0.99      | X1 = X0
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_25,negated_conjecture,
% 1.86/0.99      ( ~ v2_struct_0(sK0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_24,negated_conjecture,
% 1.86/0.99      ( v3_orders_2(sK0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_23,negated_conjecture,
% 1.86/0.99      ( v4_orders_2(sK0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_22,negated_conjecture,
% 1.86/0.99      ( v5_orders_2(sK0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_681,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 1.86/0.99      | m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | X1 = X0
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_677,c_25,c_24,c_23,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_853,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(X1,sK0,sK1)
% 1.86/0.99      | m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | X1 = X0 ),
% 1.86/0.99      inference(equality_resolution_simp,[status(thm)],[c_681]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1390,plain,
% 1.86/0.99      ( X0 = X1
% 1.86/0.99      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 1.86/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_orders_2(X0,sK0,X1) = iProver_top
% 1.86/0.99      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2483,plain,
% 1.86/0.99      ( sK3 = X0
% 1.86/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 1.86/0.99      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1399,c_1390]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2553,plain,
% 1.86/0.99      ( sK3 = sK2
% 1.86/0.99      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.86/0.99      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1398,c_2483]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_32,plain,
% 1.86/0.99      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_33,plain,
% 1.86/0.99      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1846,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.86/0.99      | m1_orders_2(X0,sK0,sK3)
% 1.86/0.99      | m1_orders_2(sK3,sK0,X0)
% 1.86/0.99      | X0 = sK3 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_853]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2315,plain,
% 1.86/0.99      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(sK2,sK0,sK1)
% 1.86/0.99      | m1_orders_2(sK3,sK0,sK2)
% 1.86/0.99      | m1_orders_2(sK2,sK0,sK3)
% 1.86/0.99      | sK2 = sK3 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_1846]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2316,plain,
% 1.86/0.99      ( sK2 = sK3
% 1.86/0.99      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.86/0.99      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.86/0.99      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2595,plain,
% 1.86/0.99      ( m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.86/0.99      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_2553,c_32,c_33,c_408,c_2316]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_10,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_537,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK1 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_538,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_537]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_655,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK0 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_538,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_656,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | v2_struct_0(sK0)
% 1.86/0.99      | ~ v3_orders_2(sK0)
% 1.86/0.99      | ~ v4_orders_2(sK0)
% 1.86/0.99      | ~ v5_orders_2(sK0)
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_655]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_660,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_656,c_25,c_24,c_23,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_857,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.86/0.99      inference(equality_resolution_simp,[status(thm)],[c_660]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1389,plain,
% 1.86/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_11,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | r1_tarski(X0,X2)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_760,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | r1_tarski(X0,X2)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | sK0 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_761,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | r1_tarski(X0,X1)
% 1.86/0.99      | v2_struct_0(sK0)
% 1.86/0.99      | ~ v3_orders_2(sK0)
% 1.86/0.99      | ~ v4_orders_2(sK0)
% 1.86/0.99      | ~ v5_orders_2(sK0) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_760]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_763,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | r1_tarski(X0,X1) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_761,c_25,c_24,c_23,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1393,plain,
% 1.86/0.99      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 1.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1670,plain,
% 1.86/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_orders_2(X1,sK0,X0) != iProver_top
% 1.86/0.99      | r1_tarski(X1,X0) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1389,c_1393]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1789,plain,
% 1.86/0.99      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 1.86/0.99      | r1_tarski(X0,sK2) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1398,c_1670]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2605,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 1.86/0.99      | r1_tarski(sK3,sK2) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_2595,c_1789]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3048,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_1395,c_398,c_408,c_2159,c_2605]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1788,plain,
% 1.86/0.99      ( m1_orders_2(X0,sK0,sK3) != iProver_top
% 1.86/0.99      | r1_tarski(X0,sK3) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1399,c_1670]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3061,plain,
% 1.86/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_3048,c_1788]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1403,plain,
% 1.86/0.99      ( X0 = X1
% 1.86/0.99      | r1_tarski(X1,X0) != iProver_top
% 1.86/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3099,plain,
% 1.86/0.99      ( sK3 = sK2 | r1_tarski(sK3,sK2) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_3061,c_1403]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_0,plain,
% 1.86/0.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_16,negated_conjecture,
% 1.86/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_193,plain,
% 1.86/0.99      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 1.86/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_194,plain,
% 1.86/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_193]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_383,plain,
% 1.86/0.99      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.86/0.99      | ~ r1_tarski(X0,X1)
% 1.86/0.99      | X1 = X0
% 1.86/0.99      | sK3 != X1
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_194]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_384,plain,
% 1.86/0.99      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_383]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_385,plain,
% 1.86/0.99      ( sK3 = sK2
% 1.86/0.99      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.86/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1524,plain,
% 1.86/0.99      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.86/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_857]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1525,plain,
% 1.86/0.99      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1540,plain,
% 1.86/0.99      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.86/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | r1_tarski(sK2,sK3) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1541,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.86/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.86/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3217,plain,
% 1.86/0.99      ( sK3 = sK2 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_3099,c_33,c_385,c_398,c_408,c_1525,c_1541,c_2159,c_2605]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3226,plain,
% 1.86/0.99      ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 1.86/0.99      inference(demodulation,[status(thm)],[c_3217,c_2595]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_12,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_xboole_0 = X2 ),
% 1.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_9,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_142,plain,
% 1.86/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.86/0.99      | ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_xboole_0 = X2 ),
% 1.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_12,c_9]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_143,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_xboole_0 = X2 ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_142]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_736,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.86/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | sK0 != X1
% 1.86/0.99      | k1_xboole_0 = X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_143,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_737,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | ~ m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | v2_struct_0(sK0)
% 1.86/0.99      | ~ v3_orders_2(sK0)
% 1.86/0.99      | ~ v4_orders_2(sK0)
% 1.86/0.99      | ~ v5_orders_2(sK0)
% 1.86/0.99      | k1_xboole_0 = X0 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_736]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_741,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | ~ m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | k1_xboole_0 = X0 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_737,c_25,c_24,c_23,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_742,plain,
% 1.86/0.99      ( ~ m1_orders_2(X0,sK0,X1)
% 1.86/0.99      | ~ m1_orders_2(X1,sK0,X0)
% 1.86/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.86/0.99      | k1_xboole_0 = X1 ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_741]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1394,plain,
% 1.86/0.99      ( k1_xboole_0 = X0
% 1.86/0.99      | m1_orders_2(X1,sK0,X0) != iProver_top
% 1.86/0.99      | m1_orders_2(X0,sK0,X1) != iProver_top
% 1.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1668,plain,
% 1.86/0.99      ( k1_xboole_0 = X0
% 1.86/0.99      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m1_orders_2(X0,sK0,X1) != iProver_top
% 1.86/0.99      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1389,c_1394]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2705,plain,
% 1.86/0.99      ( sK2 = k1_xboole_0
% 1.86/0.99      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 1.86/0.99      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1398,c_1668]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3347,plain,
% 1.86/0.99      ( sK2 = k1_xboole_0 | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_3226,c_2705]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3351,plain,
% 1.86/0.99      ( sK2 = k1_xboole_0 ),
% 1.86/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3347,c_3226]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3376,plain,
% 1.86/0.99      ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
% 1.86/0.99      inference(demodulation,[status(thm)],[c_3351,c_1398]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_6,plain,
% 1.86/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1401,plain,
% 1.86/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1981,plain,
% 1.86/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1402,c_1401]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_8,plain,
% 1.86/0.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_13,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m2_orders_2(X3,X1,X2)
% 1.86/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.86/0.99      | ~ r1_xboole_0(X0,X3)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_504,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.86/0.99      | ~ m2_orders_2(X3,X1,X2)
% 1.86/0.99      | ~ r1_xboole_0(X0,X3)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK1 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_505,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 1.86/0.99      | ~ r1_xboole_0(X2,X0)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_504]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_588,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(X2,X1,sK1)
% 1.86/0.99      | ~ r1_tarski(X3,X4)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | X2 != X3
% 1.86/0.99      | k4_xboole_0(X5,X4) != X0
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_505]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_589,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(k4_xboole_0(X2,X3),X1,sK1)
% 1.86/0.99      | ~ r1_tarski(X0,X3)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | ~ l1_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_588]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_631,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,X1,sK1)
% 1.86/0.99      | ~ m2_orders_2(k4_xboole_0(X2,X3),X1,sK1)
% 1.86/0.99      | ~ r1_tarski(X0,X3)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v3_orders_2(X1)
% 1.86/0.99      | ~ v4_orders_2(X1)
% 1.86/0.99      | ~ v5_orders_2(X1)
% 1.86/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.86/0.99      | sK0 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_589,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_632,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
% 1.86/0.99      | ~ r1_tarski(X0,X2)
% 1.86/0.99      | v2_struct_0(sK0)
% 1.86/0.99      | ~ v3_orders_2(sK0)
% 1.86/0.99      | ~ v4_orders_2(sK0)
% 1.86/0.99      | ~ v5_orders_2(sK0)
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_631]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_636,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
% 1.86/0.99      | ~ r1_tarski(X0,X2)
% 1.86/0.99      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_632,c_25,c_24,c_23,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_861,plain,
% 1.86/0.99      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.86/0.99      | ~ m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1)
% 1.86/0.99      | ~ r1_tarski(X0,X2) ),
% 1.86/0.99      inference(equality_resolution_simp,[status(thm)],[c_636]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1388,plain,
% 1.86/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m2_orders_2(k4_xboole_0(X1,X2),sK0,sK1) != iProver_top
% 1.86/0.99      | r1_tarski(X0,X2) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2537,plain,
% 1.86/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top
% 1.86/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1981,c_1388]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3907,plain,
% 1.86/0.99      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.86/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2537,c_3376]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3915,plain,
% 1.86/0.99      ( r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_3376,c_3907]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3921,plain,
% 1.86/0.99      ( $false ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1402,c_3915]) ).
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  ------                               Statistics
% 1.86/0.99  
% 1.86/0.99  ------ General
% 1.86/0.99  
% 1.86/0.99  abstr_ref_over_cycles:                  0
% 1.86/0.99  abstr_ref_under_cycles:                 0
% 1.86/0.99  gc_basic_clause_elim:                   0
% 1.86/0.99  forced_gc_time:                         0
% 1.86/0.99  parsing_time:                           0.008
% 1.86/0.99  unif_index_cands_time:                  0.
% 1.86/0.99  unif_index_add_time:                    0.
% 1.86/0.99  orderings_time:                         0.
% 1.86/0.99  out_proof_time:                         0.011
% 1.86/0.99  total_time:                             0.138
% 1.86/0.99  num_of_symbols:                         52
% 1.86/0.99  num_of_terms:                           1984
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing
% 1.86/0.99  
% 1.86/0.99  num_of_splits:                          0
% 1.86/0.99  num_of_split_atoms:                     0
% 1.86/0.99  num_of_reused_defs:                     0
% 1.86/0.99  num_eq_ax_congr_red:                    12
% 1.86/0.99  num_of_sem_filtered_clauses:            1
% 1.86/0.99  num_of_subtypes:                        0
% 1.86/0.99  monotx_restored_types:                  0
% 1.86/0.99  sat_num_of_epr_types:                   0
% 1.86/0.99  sat_num_of_non_cyclic_types:            0
% 1.86/0.99  sat_guarded_non_collapsed_types:        0
% 1.86/0.99  num_pure_diseq_elim:                    0
% 1.86/0.99  simp_replaced_by:                       0
% 1.86/0.99  res_preprocessed:                       90
% 1.86/0.99  prep_upred:                             0
% 1.86/0.99  prep_unflattend:                        22
% 1.86/0.99  smt_new_axioms:                         0
% 1.86/0.99  pred_elim_cands:                        4
% 1.86/0.99  pred_elim:                              8
% 1.86/0.99  pred_elim_cl:                           9
% 1.86/0.99  pred_elim_cycles:                       11
% 1.86/0.99  merged_defs:                            10
% 1.86/0.99  merged_defs_ncl:                        0
% 1.86/0.99  bin_hyper_res:                          10
% 1.86/0.99  prep_cycles:                            4
% 1.86/0.99  pred_elim_time:                         0.011
% 1.86/0.99  splitting_time:                         0.
% 1.86/0.99  sem_filter_time:                        0.
% 1.86/0.99  monotx_time:                            0.001
% 1.86/0.99  subtype_inf_time:                       0.
% 1.86/0.99  
% 1.86/0.99  ------ Problem properties
% 1.86/0.99  
% 1.86/0.99  clauses:                                16
% 1.86/0.99  conjectures:                            2
% 1.86/0.99  epr:                                    9
% 1.86/0.99  horn:                                   14
% 1.86/0.99  ground:                                 5
% 1.86/0.99  unary:                                  3
% 1.86/0.99  binary:                                 5
% 1.86/0.99  lits:                                   42
% 1.86/0.99  lits_eq:                                8
% 1.86/0.99  fd_pure:                                0
% 1.86/0.99  fd_pseudo:                              0
% 1.86/0.99  fd_cond:                                1
% 1.86/0.99  fd_pseudo_cond:                         3
% 1.86/0.99  ac_symbols:                             0
% 1.86/0.99  
% 1.86/0.99  ------ Propositional Solver
% 1.86/0.99  
% 1.86/0.99  prop_solver_calls:                      29
% 1.86/0.99  prop_fast_solver_calls:                 846
% 1.86/0.99  smt_solver_calls:                       0
% 1.86/0.99  smt_fast_solver_calls:                  0
% 1.86/0.99  prop_num_of_clauses:                    1188
% 1.86/0.99  prop_preprocess_simplified:             3883
% 1.86/0.99  prop_fo_subsumed:                       37
% 1.86/0.99  prop_solver_time:                       0.
% 1.86/0.99  smt_solver_time:                        0.
% 1.86/0.99  smt_fast_solver_time:                   0.
% 1.86/0.99  prop_fast_solver_time:                  0.
% 1.86/0.99  prop_unsat_core_time:                   0.
% 1.86/0.99  
% 1.86/0.99  ------ QBF
% 1.86/0.99  
% 1.86/0.99  qbf_q_res:                              0
% 1.86/0.99  qbf_num_tautologies:                    0
% 1.86/0.99  qbf_prep_cycles:                        0
% 1.86/0.99  
% 1.86/0.99  ------ BMC1
% 1.86/0.99  
% 1.86/0.99  bmc1_current_bound:                     -1
% 1.86/0.99  bmc1_last_solved_bound:                 -1
% 1.86/0.99  bmc1_unsat_core_size:                   -1
% 1.86/0.99  bmc1_unsat_core_parents_size:           -1
% 1.86/0.99  bmc1_merge_next_fun:                    0
% 1.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation
% 1.86/0.99  
% 1.86/0.99  inst_num_of_clauses:                    312
% 1.86/0.99  inst_num_in_passive:                    26
% 1.86/0.99  inst_num_in_active:                     243
% 1.86/0.99  inst_num_in_unprocessed:                43
% 1.86/0.99  inst_num_of_loops:                      250
% 1.86/0.99  inst_num_of_learning_restarts:          0
% 1.86/0.99  inst_num_moves_active_passive:          2
% 1.86/0.99  inst_lit_activity:                      0
% 1.86/0.99  inst_lit_activity_moves:                0
% 1.86/0.99  inst_num_tautologies:                   0
% 1.86/0.99  inst_num_prop_implied:                  0
% 1.86/0.99  inst_num_existing_simplified:           0
% 1.86/0.99  inst_num_eq_res_simplified:             0
% 1.86/0.99  inst_num_child_elim:                    0
% 1.86/0.99  inst_num_of_dismatching_blockings:      30
% 1.86/0.99  inst_num_of_non_proper_insts:           399
% 1.86/0.99  inst_num_of_duplicates:                 0
% 1.86/0.99  inst_inst_num_from_inst_to_res:         0
% 1.86/0.99  inst_dismatching_checking_time:         0.
% 1.86/0.99  
% 1.86/0.99  ------ Resolution
% 1.86/0.99  
% 1.86/0.99  res_num_of_clauses:                     0
% 1.86/0.99  res_num_in_passive:                     0
% 1.86/0.99  res_num_in_active:                      0
% 1.86/0.99  res_num_of_loops:                       94
% 1.86/0.99  res_forward_subset_subsumed:            72
% 1.86/0.99  res_backward_subset_subsumed:           2
% 1.86/0.99  res_forward_subsumed:                   0
% 1.86/0.99  res_backward_subsumed:                  0
% 1.86/0.99  res_forward_subsumption_resolution:     0
% 1.86/0.99  res_backward_subsumption_resolution:    0
% 1.86/0.99  res_clause_to_clause_subsumption:       154
% 1.86/0.99  res_orphan_elimination:                 0
% 1.86/0.99  res_tautology_del:                      76
% 1.86/0.99  res_num_eq_res_simplified:              4
% 1.86/0.99  res_num_sel_changes:                    0
% 1.86/0.99  res_moves_from_active_to_pass:          0
% 1.86/0.99  
% 1.86/0.99  ------ Superposition
% 1.86/0.99  
% 1.86/0.99  sup_time_total:                         0.
% 1.86/0.99  sup_time_generating:                    0.
% 1.86/0.99  sup_time_sim_full:                      0.
% 1.86/0.99  sup_time_sim_immed:                     0.
% 1.86/0.99  
% 1.86/0.99  sup_num_of_clauses:                     32
% 1.86/0.99  sup_num_in_active:                      26
% 1.86/0.99  sup_num_in_passive:                     6
% 1.86/0.99  sup_num_of_loops:                       49
% 1.86/0.99  sup_fw_superposition:                   23
% 1.86/0.99  sup_bw_superposition:                   48
% 1.86/0.99  sup_immediate_simplified:               15
% 1.86/0.99  sup_given_eliminated:                   1
% 1.86/0.99  comparisons_done:                       0
% 1.86/0.99  comparisons_avoided:                    0
% 1.86/0.99  
% 1.86/0.99  ------ Simplifications
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  sim_fw_subset_subsumed:                 6
% 1.86/0.99  sim_bw_subset_subsumed:                 9
% 1.86/0.99  sim_fw_subsumed:                        7
% 1.86/0.99  sim_bw_subsumed:                        0
% 1.86/0.99  sim_fw_subsumption_res:                 2
% 1.86/0.99  sim_bw_subsumption_res:                 0
% 1.86/0.99  sim_tautology_del:                      3
% 1.86/0.99  sim_eq_tautology_del:                   7
% 1.86/0.99  sim_eq_res_simp:                        0
% 1.86/0.99  sim_fw_demodulated:                     1
% 1.86/0.99  sim_bw_demodulated:                     23
% 1.86/0.99  sim_light_normalised:                   4
% 1.86/0.99  sim_joinable_taut:                      0
% 1.86/0.99  sim_joinable_simp:                      0
% 1.86/0.99  sim_ac_normalised:                      0
% 1.86/0.99  sim_smt_subsumption:                    0
% 1.86/0.99  
%------------------------------------------------------------------------------
