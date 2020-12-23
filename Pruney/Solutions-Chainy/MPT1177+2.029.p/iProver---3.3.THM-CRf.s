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
% DateTime   : Thu Dec  3 12:12:53 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  181 (2100 expanded)
%              Number of clauses        :  116 ( 391 expanded)
%              Number of leaves         :   18 ( 688 expanded)
%              Depth                    :   23
%              Number of atoms          :  907 (20319 expanded)
%              Number of equality atoms :  178 ( 459 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(flattening,[],[f34])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38,f37,f36])).

fof(f63,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f42])).

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

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f23])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f21])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

cnf(c_936,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1494,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X2 != sK1
    | X0 != sK3
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_1550,plain,
    ( m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X0 != sK3
    | X1 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_2504,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,X0,sK1)
    | X0 != sK0
    | sK1 != sK1
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_2506,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1342,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1343,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_491,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | m1_orders_2(X2,X1,X0)
    | m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_600,plain,
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
    inference(resolution_lifted,[status(thm)],[c_491,c_21])).

cnf(c_601,plain,
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
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_605,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_25,c_24,c_23,c_22])).

cnf(c_801,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_605])).

cnf(c_1333,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_1773,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1333])).

cnf(c_2053,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1773])).

cnf(c_32,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_33,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_194,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_195,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_391,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_195])).

cnf(c_392,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_393,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_401,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_195])).

cnf(c_402,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_403,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_529,plain,
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

cnf(c_530,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_579,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_530,c_21])).

cnf(c_580,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_25,c_24,c_23,c_22])).

cnf(c_805,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_584])).

cnf(c_1469,plain,
    ( ~ m2_orders_2(sK2,sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1470,plain,
    ( m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_1616,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1760,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_1761,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1615,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1812,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_1813,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_705,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_706,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_708,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_25,c_24,c_23,c_22])).

cnf(c_1911,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1912,plain,
    ( m1_orders_2(sK3,sK0,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_2104,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_32,c_33,c_393,c_403,c_1470,c_1761,c_1813,c_1912])).

cnf(c_1332,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_1337,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1589,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_1337])).

cnf(c_1696,plain,
    ( m1_orders_2(X0,sK0,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1589])).

cnf(c_2109,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_1696])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1345,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2222,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2109,c_1345])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f54])).

cnf(c_335,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 != X4
    | k4_xboole_0(X5,X4) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_336,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(k4_xboole_0(X3,X0),X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_421,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(k4_xboole_0(X3,X0),X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_20])).

cnf(c_422,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(k4_xboole_0(X2,X0),X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_660,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(k4_xboole_0(X2,X0),X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_21])).

cnf(c_661,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_25,c_24,c_23,c_22])).

cnf(c_793,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_665])).

cnf(c_1335,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_2492,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_1335])).

cnf(c_2497,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2492])).

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
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

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

cnf(c_681,plain,
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

cnf(c_682,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_686,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_25,c_24,c_23,c_22])).

cnf(c_687,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_686])).

cnf(c_1525,plain,
    ( ~ m1_orders_2(X0,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_2330,plain,
    ( ~ m1_orders_2(sK3,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_2106,plain,
    ( m1_orders_2(sK2,sK0,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2104])).

cnf(c_935,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1489,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X2 != sK3
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1630,plain,
    ( m1_orders_2(X0,X1,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X1 != sK0
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1841,plain,
    ( m1_orders_2(sK3,X0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X0 != sK0
    | sK3 != sK3
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1843,plain,
    ( m1_orders_2(sK3,sK0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | sK3 != sK3
    | sK3 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_929,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1631,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1551,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1482,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1483,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_1466,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1467,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_192,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_193,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_378,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_193])).

cnf(c_379,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_380,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_69,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_65,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2506,c_2497,c_2330,c_2106,c_2104,c_1843,c_1631,c_1551,c_1483,c_1467,c_1466,c_380,c_69,c_65,c_33,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.93/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.99  
% 1.93/0.99  ------  iProver source info
% 1.93/0.99  
% 1.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.99  git: non_committed_changes: false
% 1.93/0.99  git: last_make_outside_of_git: false
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     num_symb
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       true
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  ------ Parsing...
% 1.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.99  ------ Proving...
% 1.93/0.99  ------ Problem Properties 
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  clauses                                 16
% 1.93/0.99  conjectures                             2
% 1.93/0.99  EPR                                     9
% 1.93/0.99  Horn                                    14
% 1.93/0.99  unary                                   3
% 1.93/0.99  binary                                  6
% 1.93/0.99  lits                                    41
% 1.93/0.99  lits eq                                 8
% 1.93/0.99  fd_pure                                 0
% 1.93/0.99  fd_pseudo                               0
% 1.93/0.99  fd_cond                                 1
% 1.93/0.99  fd_pseudo_cond                          3
% 1.93/0.99  AC symbols                              0
% 1.93/0.99  
% 1.93/0.99  ------ Schedule dynamic 5 is on 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  Current options:
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     none
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       false
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ Proving...
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS status Theorem for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  fof(f11,conjecture,(
% 1.93/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f12,negated_conjecture,(
% 1.93/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.93/0.99    inference(negated_conjecture,[],[f11])).
% 1.93/0.99  
% 1.93/0.99  fof(f26,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f12])).
% 1.93/0.99  
% 1.93/0.99  fof(f27,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f34,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f27])).
% 1.93/0.99  
% 1.93/0.99  fof(f35,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f34])).
% 1.93/0.99  
% 1.93/0.99  fof(f39,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f38,plain,(
% 1.93/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f37,plain,(
% 1.93/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f36,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f40,plain,(
% 1.93/0.99    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38,f37,f36])).
% 1.93/0.99  
% 1.93/0.99  fof(f63,plain,(
% 1.93/0.99    m2_orders_2(sK2,sK0,sK1)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f64,plain,(
% 1.93/0.99    m2_orders_2(sK3,sK0,sK1)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f10,axiom,(
% 1.93/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f24,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f10])).
% 1.93/0.99  
% 1.93/0.99  fof(f25,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f24])).
% 1.93/0.99  
% 1.93/0.99  fof(f33,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f25])).
% 1.93/0.99  
% 1.93/0.99  fof(f56,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f33])).
% 1.93/0.99  
% 1.93/0.99  fof(f62,plain,(
% 1.93/0.99    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f61,plain,(
% 1.93/0.99    l1_orders_2(sK0)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f57,plain,(
% 1.93/0.99    ~v2_struct_0(sK0)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f58,plain,(
% 1.93/0.99    v3_orders_2(sK0)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f59,plain,(
% 1.93/0.99    v4_orders_2(sK0)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f60,plain,(
% 1.93/0.99    v5_orders_2(sK0)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f1,axiom,(
% 1.93/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f28,plain,(
% 1.93/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.93/1.00    inference(nnf_transformation,[],[f1])).
% 1.93/1.00  
% 1.93/1.00  fof(f29,plain,(
% 1.93/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.93/1.00    inference(flattening,[],[f28])).
% 1.93/1.00  
% 1.93/1.00  fof(f41,plain,(
% 1.93/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f29])).
% 1.93/1.00  
% 1.93/1.00  fof(f65,plain,(
% 1.93/1.00    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.93/1.00    inference(cnf_transformation,[],[f40])).
% 1.93/1.00  
% 1.93/1.00  fof(f42,plain,(
% 1.93/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f29])).
% 1.93/1.00  
% 1.93/1.00  fof(f67,plain,(
% 1.93/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.93/1.00    inference(equality_resolution,[],[f42])).
% 1.93/1.00  
% 1.93/1.00  fof(f6,axiom,(
% 1.93/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f13,plain,(
% 1.93/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.93/1.00    inference(pure_predicate_removal,[],[f6])).
% 1.93/1.00  
% 1.93/1.00  fof(f16,plain,(
% 1.93/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/1.00    inference(ennf_transformation,[],[f13])).
% 1.93/1.00  
% 1.93/1.00  fof(f17,plain,(
% 1.93/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/1.00    inference(flattening,[],[f16])).
% 1.93/1.00  
% 1.93/1.00  fof(f51,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f17])).
% 1.93/1.00  
% 1.93/1.00  fof(f2,axiom,(
% 1.93/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f30,plain,(
% 1.93/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/1.00    inference(nnf_transformation,[],[f2])).
% 1.93/1.00  
% 1.93/1.00  fof(f31,plain,(
% 1.93/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/1.00    inference(flattening,[],[f30])).
% 1.93/1.00  
% 1.93/1.00  fof(f46,plain,(
% 1.93/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f31])).
% 1.93/1.00  
% 1.93/1.00  fof(f7,axiom,(
% 1.93/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f18,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/1.00    inference(ennf_transformation,[],[f7])).
% 1.93/1.00  
% 1.93/1.00  fof(f19,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/1.00    inference(flattening,[],[f18])).
% 1.93/1.00  
% 1.93/1.00  fof(f52,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f19])).
% 1.93/1.00  
% 1.93/1.00  fof(f3,axiom,(
% 1.93/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f32,plain,(
% 1.93/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.93/1.00    inference(nnf_transformation,[],[f3])).
% 1.93/1.00  
% 1.93/1.00  fof(f48,plain,(
% 1.93/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f32])).
% 1.93/1.00  
% 1.93/1.00  fof(f4,axiom,(
% 1.93/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f49,plain,(
% 1.93/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f4])).
% 1.93/1.00  
% 1.93/1.00  fof(f9,axiom,(
% 1.93/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f22,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/1.00    inference(ennf_transformation,[],[f9])).
% 1.93/1.00  
% 1.93/1.00  fof(f23,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/1.00    inference(flattening,[],[f22])).
% 1.93/1.00  
% 1.93/1.00  fof(f54,plain,(
% 1.93/1.00    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f23])).
% 1.93/1.00  
% 1.93/1.00  fof(f8,axiom,(
% 1.93/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f20,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/1.00    inference(ennf_transformation,[],[f8])).
% 1.93/1.00  
% 1.93/1.00  fof(f21,plain,(
% 1.93/1.00    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/1.00    inference(flattening,[],[f20])).
% 1.93/1.00  
% 1.93/1.00  fof(f53,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f21])).
% 1.93/1.00  
% 1.93/1.00  fof(f5,axiom,(
% 1.93/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.00  
% 1.93/1.00  fof(f14,plain,(
% 1.93/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.93/1.00    inference(ennf_transformation,[],[f5])).
% 1.93/1.00  
% 1.93/1.00  fof(f15,plain,(
% 1.93/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.93/1.00    inference(flattening,[],[f14])).
% 1.93/1.00  
% 1.93/1.00  fof(f50,plain,(
% 1.93/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f15])).
% 1.93/1.00  
% 1.93/1.00  fof(f43,plain,(
% 1.93/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.93/1.00    inference(cnf_transformation,[],[f29])).
% 1.93/1.00  
% 1.93/1.00  fof(f66,plain,(
% 1.93/1.00    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.93/1.00    inference(cnf_transformation,[],[f40])).
% 1.93/1.00  
% 1.93/1.00  fof(f44,plain,(
% 1.93/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.93/1.00    inference(cnf_transformation,[],[f31])).
% 1.93/1.00  
% 1.93/1.00  fof(f69,plain,(
% 1.93/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.93/1.00    inference(equality_resolution,[],[f44])).
% 1.93/1.00  
% 1.93/1.00  cnf(c_936,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | m2_orders_2(X3,X4,X5)
% 1.93/1.00      | X3 != X0
% 1.93/1.00      | X4 != X1
% 1.93/1.00      | X5 != X2 ),
% 1.93/1.00      theory(equality) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1494,plain,
% 1.93/1.00      ( m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | X2 != sK1
% 1.93/1.00      | X0 != sK3
% 1.93/1.00      | X1 != sK0 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_936]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1550,plain,
% 1.93/1.00      ( m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | X0 != sK3
% 1.93/1.00      | X1 != sK0
% 1.93/1.00      | sK1 != sK1 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1494]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2504,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | m2_orders_2(k1_xboole_0,X0,sK1)
% 1.93/1.00      | X0 != sK0
% 1.93/1.00      | sK1 != sK1
% 1.93/1.00      | k1_xboole_0 != sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1550]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2506,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | m2_orders_2(k1_xboole_0,sK0,sK1)
% 1.93/1.00      | sK1 != sK1
% 1.93/1.00      | sK0 != sK0
% 1.93/1.00      | k1_xboole_0 != sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_2504]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_19,negated_conjecture,
% 1.93/1.00      ( m2_orders_2(sK2,sK0,sK1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1342,plain,
% 1.93/1.00      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_18,negated_conjecture,
% 1.93/1.00      ( m2_orders_2(sK3,sK0,sK1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1343,plain,
% 1.93/1.00      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_14,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.93/1.00      | m1_orders_2(X3,X1,X0)
% 1.93/1.00      | m1_orders_2(X0,X1,X3)
% 1.93/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | X3 = X0 ),
% 1.93/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_20,negated_conjecture,
% 1.93/1.00      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 1.93/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_490,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.93/1.00      | m1_orders_2(X3,X1,X0)
% 1.93/1.00      | m1_orders_2(X0,X1,X3)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | X3 = X0
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK1 != X2 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_491,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 1.93/1.00      | m1_orders_2(X2,X1,X0)
% 1.93/1.00      | m1_orders_2(X0,X1,X2)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | X2 = X0
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_21,negated_conjecture,
% 1.93/1.00      ( l1_orders_2(sK0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_600,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 1.93/1.00      | m1_orders_2(X0,X1,X2)
% 1.93/1.00      | m1_orders_2(X2,X1,X0)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | X2 = X0
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK0 != X1 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_491,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_601,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 1.93/1.00      | m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | v2_struct_0(sK0)
% 1.93/1.00      | ~ v3_orders_2(sK0)
% 1.93/1.00      | ~ v4_orders_2(sK0)
% 1.93/1.00      | ~ v5_orders_2(sK0)
% 1.93/1.00      | X1 = X0
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_600]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_25,negated_conjecture,
% 1.93/1.00      ( ~ v2_struct_0(sK0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_24,negated_conjecture,
% 1.93/1.00      ( v3_orders_2(sK0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_23,negated_conjecture,
% 1.93/1.00      ( v4_orders_2(sK0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_22,negated_conjecture,
% 1.93/1.00      ( v5_orders_2(sK0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_605,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 1.93/1.00      | m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | X1 = X0
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_601,c_25,c_24,c_23,c_22]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_801,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 1.93/1.00      | m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | X1 = X0 ),
% 1.93/1.00      inference(equality_resolution_simp,[status(thm)],[c_605]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1333,plain,
% 1.93/1.00      ( X0 = X1
% 1.93/1.00      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 1.93/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_orders_2(X0,sK0,X1) = iProver_top
% 1.93/1.00      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1773,plain,
% 1.93/1.00      ( sK3 = X0
% 1.93/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 1.93/1.00      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1343,c_1333]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2053,plain,
% 1.93/1.00      ( sK3 = sK2
% 1.93/1.00      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.93/1.00      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1342,c_1773]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_32,plain,
% 1.93/1.00      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_33,plain,
% 1.93/1.00      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2,plain,
% 1.93/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_17,negated_conjecture,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.93/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_194,plain,
% 1.93/1.00      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 1.93/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_195,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.93/1.00      inference(renaming,[status(thm)],[c_194]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_391,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | r1_tarski(X0,X1)
% 1.93/1.00      | sK3 != X1
% 1.93/1.00      | sK2 != X0 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_195]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_392,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_393,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 1.93/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1,plain,
% 1.93/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_401,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_195]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_402,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_403,plain,
% 1.93/1.00      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_10,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_529,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK1 != X2 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_530,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_529]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_579,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK0 != X1 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_530,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_580,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | v2_struct_0(sK0)
% 1.93/1.00      | ~ v3_orders_2(sK0)
% 1.93/1.00      | ~ v4_orders_2(sK0)
% 1.93/1.00      | ~ v5_orders_2(sK0)
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_579]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_584,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_580,c_25,c_24,c_23,c_22]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_805,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.93/1.00      inference(equality_resolution_simp,[status(thm)],[c_584]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1469,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK2,sK0,sK1)
% 1.93/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_805]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1470,plain,
% 1.93/1.00      ( m2_orders_2(sK2,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1469]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1616,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | m1_orders_2(X0,sK0,sK3)
% 1.93/1.00      | m1_orders_2(sK3,sK0,X0)
% 1.93/1.00      | X0 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_801]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1760,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(sK2,sK0,sK1)
% 1.93/1.00      | m1_orders_2(sK3,sK0,sK2)
% 1.93/1.00      | m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | sK2 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1616]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1761,plain,
% 1.93/1.00      ( sK2 = sK3
% 1.93/1.00      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.93/1.00      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.93/1.00      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_3,plain,
% 1.93/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.93/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1615,plain,
% 1.93/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1812,plain,
% 1.93/1.00      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1615]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1813,plain,
% 1.93/1.00      ( sK2 = sK3
% 1.93/1.00      | r1_tarski(sK3,sK2) != iProver_top
% 1.93/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_11,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | r1_tarski(X0,X2)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_705,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | r1_tarski(X0,X2)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | sK0 != X1 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_706,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | r1_tarski(X0,X1)
% 1.93/1.00      | v2_struct_0(sK0)
% 1.93/1.00      | ~ v3_orders_2(sK0)
% 1.93/1.00      | ~ v4_orders_2(sK0)
% 1.93/1.00      | ~ v5_orders_2(sK0) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_705]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_708,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | r1_tarski(X0,X1) ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_706,c_25,c_24,c_23,c_22]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1911,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK3,sK0,sK2)
% 1.93/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | r1_tarski(sK3,sK2) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_708]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1912,plain,
% 1.93/1.00      ( m1_orders_2(sK3,sK0,sK2) != iProver_top
% 1.93/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.93/1.00      | r1_tarski(sK3,sK2) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2104,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_2053,c_32,c_33,c_393,c_403,c_1470,c_1761,c_1813,
% 1.93/1.00                 c_1912]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1332,plain,
% 1.93/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1337,plain,
% 1.93/1.00      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 1.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.93/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1589,plain,
% 1.93/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 1.93/1.00      | r1_tarski(X1,X0) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1332,c_1337]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1696,plain,
% 1.93/1.00      ( m1_orders_2(X0,sK0,sK3) != iProver_top
% 1.93/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_1343,c_1589]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2109,plain,
% 1.93/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_2104,c_1696]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_6,plain,
% 1.93/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.93/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1345,plain,
% 1.93/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 1.93/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2222,plain,
% 1.93/1.00      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_2109,c_1345]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_8,plain,
% 1.93/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_13,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.93/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.93/1.00      | ~ r1_xboole_0(X0,X3)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_335,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.93/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | X0 != X4
% 1.93/1.00      | k4_xboole_0(X5,X4) != X3 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_336,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X3,X0),X1,X2)
% 1.93/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_335]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_421,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X3,X0),X1,X2)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK1 != X2 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_336,c_20]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_422,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X2,X0),X1,sK1)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_660,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X2,X0),X1,sK1)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.93/1.00      | sK0 != X1 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_422,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_661,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1)
% 1.93/1.00      | v2_struct_0(sK0)
% 1.93/1.00      | ~ v3_orders_2(sK0)
% 1.93/1.00      | ~ v4_orders_2(sK0)
% 1.93/1.00      | ~ v5_orders_2(sK0)
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_660]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_665,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1)
% 1.93/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_661,c_25,c_24,c_23,c_22]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_793,plain,
% 1.93/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.93/1.00      | ~ m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1) ),
% 1.93/1.00      inference(equality_resolution_simp,[status(thm)],[c_665]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1335,plain,
% 1.93/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.93/1.00      | m2_orders_2(k4_xboole_0(X1,X0),sK0,sK1) != iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2492,plain,
% 1.93/1.00      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.93/1.00      | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 1.93/1.00      inference(superposition,[status(thm)],[c_2222,c_1335]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2497,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK3,sK0,sK1) | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
% 1.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2492]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_12,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_xboole_0 = X2 ),
% 1.93/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_9,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1) ),
% 1.93/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_142,plain,
% 1.93/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.93/1.00      | ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_xboole_0 = X2 ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_12,c_9]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_143,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | ~ l1_orders_2(X1)
% 1.93/1.00      | k1_xboole_0 = X2 ),
% 1.93/1.00      inference(renaming,[status(thm)],[c_142]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_681,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.93/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.00      | v2_struct_0(X1)
% 1.93/1.00      | ~ v3_orders_2(X1)
% 1.93/1.00      | ~ v4_orders_2(X1)
% 1.93/1.00      | ~ v5_orders_2(X1)
% 1.93/1.00      | sK0 != X1
% 1.93/1.00      | k1_xboole_0 = X2 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_143,c_21]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_682,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | v2_struct_0(sK0)
% 1.93/1.00      | ~ v3_orders_2(sK0)
% 1.93/1.00      | ~ v4_orders_2(sK0)
% 1.93/1.00      | ~ v5_orders_2(sK0)
% 1.93/1.00      | k1_xboole_0 = X0 ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_681]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_686,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | k1_xboole_0 = X0 ),
% 1.93/1.00      inference(global_propositional_subsumption,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_682,c_25,c_24,c_23,c_22]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_687,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 1.93/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 1.93/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | k1_xboole_0 = X1 ),
% 1.93/1.00      inference(renaming,[status(thm)],[c_686]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1525,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,sK0,sK3)
% 1.93/1.00      | ~ m1_orders_2(sK3,sK0,X0)
% 1.93/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | k1_xboole_0 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_687]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2330,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK3,sK0,sK3)
% 1.93/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | k1_xboole_0 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1525]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_2106,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) ),
% 1.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2104]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_935,plain,
% 1.93/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.93/1.00      | m1_orders_2(X3,X4,X5)
% 1.93/1.00      | X3 != X0
% 1.93/1.00      | X4 != X1
% 1.93/1.00      | X5 != X2 ),
% 1.93/1.00      theory(equality) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1489,plain,
% 1.93/1.00      ( m1_orders_2(X0,X1,X2)
% 1.93/1.00      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | X2 != sK3
% 1.93/1.00      | X1 != sK0
% 1.93/1.00      | X0 != sK2 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1630,plain,
% 1.93/1.00      ( m1_orders_2(X0,X1,sK3)
% 1.93/1.00      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | X1 != sK0
% 1.93/1.00      | X0 != sK2
% 1.93/1.00      | sK3 != sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1489]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1841,plain,
% 1.93/1.00      ( m1_orders_2(sK3,X0,sK3)
% 1.93/1.00      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | X0 != sK0
% 1.93/1.00      | sK3 != sK3
% 1.93/1.00      | sK3 != sK2 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1630]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1843,plain,
% 1.93/1.00      ( m1_orders_2(sK3,sK0,sK3)
% 1.93/1.00      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | sK3 != sK3
% 1.93/1.00      | sK3 != sK2
% 1.93/1.00      | sK0 != sK0 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_1841]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_929,plain,( X0 = X0 ),theory(equality) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1631,plain,
% 1.93/1.00      ( sK3 = sK3 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1551,plain,
% 1.93/1.00      ( sK1 = sK1 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1482,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.00      | r1_tarski(sK2,sK3) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_708]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1483,plain,
% 1.93/1.00      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.93/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.93/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1466,plain,
% 1.93/1.00      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.93/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_805]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_1467,plain,
% 1.93/1.00      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.93/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_0,plain,
% 1.93/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.93/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_16,negated_conjecture,
% 1.93/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.93/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_192,plain,
% 1.93/1.00      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 1.93/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_193,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.93/1.00      inference(renaming,[status(thm)],[c_192]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_378,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.93/1.00      | ~ r1_tarski(X0,X1)
% 1.93/1.00      | X1 = X0
% 1.93/1.00      | sK3 != X1
% 1.93/1.00      | sK2 != X0 ),
% 1.93/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_193]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_379,plain,
% 1.93/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 1.93/1.00      inference(unflattening,[status(thm)],[c_378]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_380,plain,
% 1.93/1.00      ( sK3 = sK2
% 1.93/1.00      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.93/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.93/1.00      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_69,plain,
% 1.93/1.00      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_5,plain,
% 1.93/1.00      ( r1_tarski(X0,X0) ),
% 1.93/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(c_65,plain,
% 1.93/1.00      ( r1_tarski(sK0,sK0) ),
% 1.93/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.93/1.00  
% 1.93/1.00  cnf(contradiction,plain,
% 1.93/1.00      ( $false ),
% 1.93/1.00      inference(minisat,
% 1.93/1.00                [status(thm)],
% 1.93/1.00                [c_2506,c_2497,c_2330,c_2106,c_2104,c_1843,c_1631,c_1551,
% 1.93/1.00                 c_1483,c_1467,c_1466,c_380,c_69,c_65,c_33,c_18]) ).
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/1.00  
% 1.93/1.00  ------                               Statistics
% 1.93/1.00  
% 1.93/1.00  ------ General
% 1.93/1.00  
% 1.93/1.00  abstr_ref_over_cycles:                  0
% 1.93/1.00  abstr_ref_under_cycles:                 0
% 1.93/1.00  gc_basic_clause_elim:                   0
% 1.93/1.00  forced_gc_time:                         0
% 1.93/1.00  parsing_time:                           0.012
% 1.93/1.00  unif_index_cands_time:                  0.
% 1.93/1.00  unif_index_add_time:                    0.
% 1.93/1.00  orderings_time:                         0.
% 1.93/1.00  out_proof_time:                         0.016
% 1.93/1.00  total_time:                             0.109
% 1.93/1.00  num_of_symbols:                         52
% 1.93/1.00  num_of_terms:                           1335
% 1.93/1.00  
% 1.93/1.00  ------ Preprocessing
% 1.93/1.00  
% 1.93/1.00  num_of_splits:                          0
% 1.93/1.00  num_of_split_atoms:                     0
% 1.93/1.00  num_of_reused_defs:                     0
% 1.93/1.00  num_eq_ax_congr_red:                    12
% 1.93/1.00  num_of_sem_filtered_clauses:            1
% 1.93/1.00  num_of_subtypes:                        0
% 1.93/1.00  monotx_restored_types:                  0
% 1.93/1.00  sat_num_of_epr_types:                   0
% 1.93/1.00  sat_num_of_non_cyclic_types:            0
% 1.93/1.00  sat_guarded_non_collapsed_types:        0
% 1.93/1.00  num_pure_diseq_elim:                    0
% 1.93/1.00  simp_replaced_by:                       0
% 1.93/1.00  res_preprocessed:                       90
% 1.93/1.00  prep_upred:                             0
% 1.93/1.00  prep_unflattend:                        20
% 1.93/1.00  smt_new_axioms:                         0
% 1.93/1.00  pred_elim_cands:                        4
% 1.93/1.00  pred_elim:                              8
% 1.93/1.00  pred_elim_cl:                           9
% 1.93/1.00  pred_elim_cycles:                       10
% 1.93/1.00  merged_defs:                            10
% 1.93/1.00  merged_defs_ncl:                        0
% 1.93/1.00  bin_hyper_res:                          10
% 1.93/1.00  prep_cycles:                            4
% 1.93/1.00  pred_elim_time:                         0.01
% 1.93/1.00  splitting_time:                         0.
% 1.93/1.00  sem_filter_time:                        0.
% 1.93/1.00  monotx_time:                            0.
% 1.93/1.00  subtype_inf_time:                       0.
% 1.93/1.00  
% 1.93/1.00  ------ Problem properties
% 1.93/1.00  
% 1.93/1.00  clauses:                                16
% 1.93/1.00  conjectures:                            2
% 1.93/1.00  epr:                                    9
% 1.93/1.00  horn:                                   14
% 1.93/1.00  ground:                                 5
% 1.93/1.00  unary:                                  3
% 1.93/1.00  binary:                                 6
% 1.93/1.00  lits:                                   41
% 1.93/1.00  lits_eq:                                8
% 1.93/1.00  fd_pure:                                0
% 1.93/1.00  fd_pseudo:                              0
% 1.93/1.00  fd_cond:                                1
% 1.93/1.00  fd_pseudo_cond:                         3
% 1.93/1.00  ac_symbols:                             0
% 1.93/1.00  
% 1.93/1.00  ------ Propositional Solver
% 1.93/1.00  
% 1.93/1.00  prop_solver_calls:                      27
% 1.93/1.00  prop_fast_solver_calls:                 743
% 1.93/1.00  smt_solver_calls:                       0
% 1.93/1.00  smt_fast_solver_calls:                  0
% 1.93/1.00  prop_num_of_clauses:                    702
% 1.93/1.00  prop_preprocess_simplified:             3129
% 1.93/1.00  prop_fo_subsumed:                       32
% 1.93/1.00  prop_solver_time:                       0.
% 1.93/1.00  smt_solver_time:                        0.
% 1.93/1.00  smt_fast_solver_time:                   0.
% 1.93/1.00  prop_fast_solver_time:                  0.
% 1.93/1.00  prop_unsat_core_time:                   0.
% 1.93/1.00  
% 1.93/1.00  ------ QBF
% 1.93/1.00  
% 1.93/1.00  qbf_q_res:                              0
% 1.93/1.00  qbf_num_tautologies:                    0
% 1.93/1.00  qbf_prep_cycles:                        0
% 1.93/1.00  
% 1.93/1.00  ------ BMC1
% 1.93/1.00  
% 1.93/1.00  bmc1_current_bound:                     -1
% 1.93/1.00  bmc1_last_solved_bound:                 -1
% 1.93/1.00  bmc1_unsat_core_size:                   -1
% 1.93/1.00  bmc1_unsat_core_parents_size:           -1
% 1.93/1.00  bmc1_merge_next_fun:                    0
% 1.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.93/1.00  
% 1.93/1.00  ------ Instantiation
% 1.93/1.00  
% 1.93/1.00  inst_num_of_clauses:                    179
% 1.93/1.00  inst_num_in_passive:                    59
% 1.93/1.00  inst_num_in_active:                     118
% 1.93/1.00  inst_num_in_unprocessed:                1
% 1.93/1.00  inst_num_of_loops:                      124
% 1.93/1.00  inst_num_of_learning_restarts:          0
% 1.93/1.00  inst_num_moves_active_passive:          1
% 1.93/1.00  inst_lit_activity:                      0
% 1.93/1.00  inst_lit_activity_moves:                0
% 1.93/1.00  inst_num_tautologies:                   0
% 1.93/1.00  inst_num_prop_implied:                  0
% 1.93/1.00  inst_num_existing_simplified:           0
% 1.93/1.00  inst_num_eq_res_simplified:             0
% 1.93/1.00  inst_num_child_elim:                    0
% 1.93/1.00  inst_num_of_dismatching_blockings:      6
% 1.93/1.00  inst_num_of_non_proper_insts:           149
% 1.93/1.00  inst_num_of_duplicates:                 0
% 1.93/1.00  inst_inst_num_from_inst_to_res:         0
% 1.93/1.00  inst_dismatching_checking_time:         0.
% 1.93/1.00  
% 1.93/1.00  ------ Resolution
% 1.93/1.00  
% 1.93/1.00  res_num_of_clauses:                     0
% 1.93/1.00  res_num_in_passive:                     0
% 1.93/1.00  res_num_in_active:                      0
% 1.93/1.00  res_num_of_loops:                       94
% 1.93/1.00  res_forward_subset_subsumed:            20
% 1.93/1.00  res_backward_subset_subsumed:           2
% 1.93/1.00  res_forward_subsumed:                   0
% 1.93/1.00  res_backward_subsumed:                  0
% 1.93/1.00  res_forward_subsumption_resolution:     0
% 1.93/1.00  res_backward_subsumption_resolution:    0
% 1.93/1.00  res_clause_to_clause_subsumption:       76
% 1.93/1.00  res_orphan_elimination:                 0
% 1.93/1.00  res_tautology_del:                      48
% 1.93/1.00  res_num_eq_res_simplified:              4
% 1.93/1.00  res_num_sel_changes:                    0
% 1.93/1.00  res_moves_from_active_to_pass:          0
% 1.93/1.00  
% 1.93/1.00  ------ Superposition
% 1.93/1.00  
% 1.93/1.00  sup_time_total:                         0.
% 1.93/1.00  sup_time_generating:                    0.
% 1.93/1.00  sup_time_sim_full:                      0.
% 1.93/1.00  sup_time_sim_immed:                     0.
% 1.93/1.00  
% 1.93/1.00  sup_num_of_clauses:                     37
% 1.93/1.00  sup_num_in_active:                      24
% 1.93/1.00  sup_num_in_passive:                     13
% 1.93/1.00  sup_num_of_loops:                       24
% 1.93/1.00  sup_fw_superposition:                   14
% 1.93/1.00  sup_bw_superposition:                   13
% 1.93/1.00  sup_immediate_simplified:               0
% 1.93/1.00  sup_given_eliminated:                   0
% 1.93/1.00  comparisons_done:                       0
% 1.93/1.00  comparisons_avoided:                    0
% 1.93/1.00  
% 1.93/1.00  ------ Simplifications
% 1.93/1.00  
% 1.93/1.00  
% 1.93/1.00  sim_fw_subset_subsumed:                 0
% 1.93/1.00  sim_bw_subset_subsumed:                 1
% 1.93/1.00  sim_fw_subsumed:                        0
% 1.93/1.00  sim_bw_subsumed:                        0
% 1.93/1.00  sim_fw_subsumption_res:                 0
% 1.93/1.00  sim_bw_subsumption_res:                 0
% 1.93/1.00  sim_tautology_del:                      0
% 1.93/1.00  sim_eq_tautology_del:                   2
% 1.93/1.00  sim_eq_res_simp:                        0
% 1.93/1.00  sim_fw_demodulated:                     0
% 1.93/1.00  sim_bw_demodulated:                     0
% 1.93/1.00  sim_light_normalised:                   0
% 1.93/1.00  sim_joinable_taut:                      0
% 1.93/1.00  sim_joinable_simp:                      0
% 1.93/1.00  sim_ac_normalised:                      0
% 1.93/1.00  sim_smt_subsumption:                    0
% 1.93/1.00  
%------------------------------------------------------------------------------
