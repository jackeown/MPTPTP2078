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
% DateTime   : Thu Dec  3 12:12:56 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  177 (1135 expanded)
%              Number of clauses        :  115 ( 213 expanded)
%              Number of leaves         :   17 ( 373 expanded)
%              Depth                    :   21
%              Number of atoms          :  909 (10924 expanded)
%              Number of equality atoms :  190 ( 267 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).

fof(f59,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

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
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f61,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
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

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f5])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

cnf(c_1059,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1444,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X2 != sK1
    | X0 != sK3
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1501,plain,
    ( m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X0 != sK3
    | X1 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_2138,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,X0,sK1)
    | X0 != sK0
    | sK1 != sK1
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_2140,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_18,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1321,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1322,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
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
    | X0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_510,plain,
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
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_511,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_721,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_511,c_20])).

cnf(c_722,plain,
    ( m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_726,plain,
    ( m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_24,c_23,c_22,c_21])).

cnf(c_974,plain,
    ( m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_726])).

cnf(c_1312,plain,
    ( X0 = X1
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_1775,plain,
    ( sK3 = X0
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1312])).

cnf(c_2082,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_1775])).

cnf(c_31,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_32,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_179,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_180,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_391,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_180])).

cnf(c_392,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_393,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1538,plain,
    ( m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1699,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_1700,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_2091,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_31,c_32,c_393,c_1700])).

cnf(c_8,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_441,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_442,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_781,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_20])).

cnf(c_782,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_24,c_23,c_22,c_21])).

cnf(c_9,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_844,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_845,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_847,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_24,c_23,c_22,c_21])).

cnf(c_921,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m2_orders_2(X2,sK0,sK1)
    | r1_tarski(X0,X1)
    | X1 != X2
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_786,c_847])).

cnf(c_922,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_1316,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_1520,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_1316])).

cnf(c_2097,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_1520])).

cnf(c_2098,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2097])).

cnf(c_14,plain,
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
    | X0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_471,plain,
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
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_472,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_751,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_20])).

cnf(c_752,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_756,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_24,c_23,c_22,c_21])).

cnf(c_970,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_756])).

cnf(c_1313,plain,
    ( X0 = X1
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_1650,plain,
    ( sK3 = X0
    | m1_orders_2(X0,sK0,sK3) != iProver_top
    | m1_orders_2(sK3,sK0,X0) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1313])).

cnf(c_1980,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_1650])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_177,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_178,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_368,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_178])).

cnf(c_369,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_370,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1437,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_1438,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1437])).

cnf(c_2043,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_32,c_370,c_1438])).

cnf(c_2045,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | sK3 = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2043])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1323,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_325,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 != X3
    | k1_funct_1(X2,u1_struct_0(X1)) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_326,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_411,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_19])).

cnf(c_412,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_802,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_20])).

cnf(c_803,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_807,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_24,c_23,c_22,c_21])).

cnf(c_966,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_807])).

cnf(c_1314,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_1801,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1314])).

cnf(c_1802,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1801])).

cnf(c_1060,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1454,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X2 != sK3
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_1553,plain,
    ( m1_orders_2(X0,X1,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X1 != sK0
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1751,plain,
    ( m1_orders_2(sK3,X0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X0 != sK0
    | sK3 != sK3
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1753,plain,
    ( m1_orders_2(sK3,sK0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | sK3 != sK3
    | sK3 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1548,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1724,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1055,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1554,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1502,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_823,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_824,plain,
    ( ~ m1_orders_2(X0,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( ~ m1_orders_2(X0,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_24,c_23,c_22,c_21])).

cnf(c_894,plain,
    ( ~ m1_orders_2(X0,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0))
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_786,c_828])).

cnf(c_962,plain,
    ( ~ m1_orders_2(X0,sK0,X0)
    | ~ m2_orders_2(X0,sK0,sK1)
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_894])).

cnf(c_1431,plain,
    ( ~ m1_orders_2(sK3,sK0,sK3)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_381,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_180])).

cnf(c_382,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_67,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_63,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2140,c_2098,c_2045,c_1802,c_1753,c_1724,c_1554,c_1502,c_1431,c_392,c_382,c_67,c_63,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n016.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:54:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 1.53/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/0.96  
% 1.53/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/0.96  
% 1.53/0.96  ------  iProver source info
% 1.53/0.96  
% 1.53/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.53/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/0.96  git: non_committed_changes: false
% 1.53/0.96  git: last_make_outside_of_git: false
% 1.53/0.96  
% 1.53/0.96  ------ 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options
% 1.53/0.96  
% 1.53/0.96  --out_options                           all
% 1.53/0.96  --tptp_safe_out                         true
% 1.53/0.96  --problem_path                          ""
% 1.53/0.96  --include_path                          ""
% 1.53/0.96  --clausifier                            res/vclausify_rel
% 1.53/0.96  --clausifier_options                    --mode clausify
% 1.53/0.96  --stdin                                 false
% 1.53/0.96  --stats_out                             all
% 1.53/0.96  
% 1.53/0.96  ------ General Options
% 1.53/0.96  
% 1.53/0.96  --fof                                   false
% 1.53/0.96  --time_out_real                         305.
% 1.53/0.96  --time_out_virtual                      -1.
% 1.53/0.96  --symbol_type_check                     false
% 1.53/0.96  --clausify_out                          false
% 1.53/0.96  --sig_cnt_out                           false
% 1.53/0.96  --trig_cnt_out                          false
% 1.53/0.96  --trig_cnt_out_tolerance                1.
% 1.53/0.96  --trig_cnt_out_sk_spl                   false
% 1.53/0.96  --abstr_cl_out                          false
% 1.53/0.96  
% 1.53/0.96  ------ Global Options
% 1.53/0.96  
% 1.53/0.96  --schedule                              default
% 1.53/0.96  --add_important_lit                     false
% 1.53/0.96  --prop_solver_per_cl                    1000
% 1.53/0.96  --min_unsat_core                        false
% 1.53/0.96  --soft_assumptions                      false
% 1.53/0.96  --soft_lemma_size                       3
% 1.53/0.96  --prop_impl_unit_size                   0
% 1.53/0.96  --prop_impl_unit                        []
% 1.53/0.96  --share_sel_clauses                     true
% 1.53/0.96  --reset_solvers                         false
% 1.53/0.96  --bc_imp_inh                            [conj_cone]
% 1.53/0.96  --conj_cone_tolerance                   3.
% 1.53/0.96  --extra_neg_conj                        none
% 1.53/0.96  --large_theory_mode                     true
% 1.53/0.96  --prolific_symb_bound                   200
% 1.53/0.96  --lt_threshold                          2000
% 1.53/0.96  --clause_weak_htbl                      true
% 1.53/0.96  --gc_record_bc_elim                     false
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing Options
% 1.53/0.96  
% 1.53/0.96  --preprocessing_flag                    true
% 1.53/0.96  --time_out_prep_mult                    0.1
% 1.53/0.96  --splitting_mode                        input
% 1.53/0.96  --splitting_grd                         true
% 1.53/0.96  --splitting_cvd                         false
% 1.53/0.96  --splitting_cvd_svl                     false
% 1.53/0.96  --splitting_nvd                         32
% 1.53/0.96  --sub_typing                            true
% 1.53/0.96  --prep_gs_sim                           true
% 1.53/0.96  --prep_unflatten                        true
% 1.53/0.96  --prep_res_sim                          true
% 1.53/0.96  --prep_upred                            true
% 1.53/0.96  --prep_sem_filter                       exhaustive
% 1.53/0.96  --prep_sem_filter_out                   false
% 1.53/0.96  --pred_elim                             true
% 1.53/0.96  --res_sim_input                         true
% 1.53/0.96  --eq_ax_congr_red                       true
% 1.53/0.96  --pure_diseq_elim                       true
% 1.53/0.96  --brand_transform                       false
% 1.53/0.96  --non_eq_to_eq                          false
% 1.53/0.96  --prep_def_merge                        true
% 1.53/0.96  --prep_def_merge_prop_impl              false
% 1.53/0.96  --prep_def_merge_mbd                    true
% 1.53/0.96  --prep_def_merge_tr_red                 false
% 1.53/0.96  --prep_def_merge_tr_cl                  false
% 1.53/0.96  --smt_preprocessing                     true
% 1.53/0.96  --smt_ac_axioms                         fast
% 1.53/0.96  --preprocessed_out                      false
% 1.53/0.96  --preprocessed_stats                    false
% 1.53/0.96  
% 1.53/0.96  ------ Abstraction refinement Options
% 1.53/0.96  
% 1.53/0.96  --abstr_ref                             []
% 1.53/0.96  --abstr_ref_prep                        false
% 1.53/0.96  --abstr_ref_until_sat                   false
% 1.53/0.96  --abstr_ref_sig_restrict                funpre
% 1.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.96  --abstr_ref_under                       []
% 1.53/0.96  
% 1.53/0.96  ------ SAT Options
% 1.53/0.96  
% 1.53/0.96  --sat_mode                              false
% 1.53/0.96  --sat_fm_restart_options                ""
% 1.53/0.96  --sat_gr_def                            false
% 1.53/0.96  --sat_epr_types                         true
% 1.53/0.96  --sat_non_cyclic_types                  false
% 1.53/0.96  --sat_finite_models                     false
% 1.53/0.96  --sat_fm_lemmas                         false
% 1.53/0.96  --sat_fm_prep                           false
% 1.53/0.96  --sat_fm_uc_incr                        true
% 1.53/0.96  --sat_out_model                         small
% 1.53/0.96  --sat_out_clauses                       false
% 1.53/0.96  
% 1.53/0.96  ------ QBF Options
% 1.53/0.96  
% 1.53/0.96  --qbf_mode                              false
% 1.53/0.96  --qbf_elim_univ                         false
% 1.53/0.96  --qbf_dom_inst                          none
% 1.53/0.96  --qbf_dom_pre_inst                      false
% 1.53/0.96  --qbf_sk_in                             false
% 1.53/0.96  --qbf_pred_elim                         true
% 1.53/0.96  --qbf_split                             512
% 1.53/0.96  
% 1.53/0.96  ------ BMC1 Options
% 1.53/0.96  
% 1.53/0.96  --bmc1_incremental                      false
% 1.53/0.96  --bmc1_axioms                           reachable_all
% 1.53/0.96  --bmc1_min_bound                        0
% 1.53/0.96  --bmc1_max_bound                        -1
% 1.53/0.96  --bmc1_max_bound_default                -1
% 1.53/0.96  --bmc1_symbol_reachability              true
% 1.53/0.96  --bmc1_property_lemmas                  false
% 1.53/0.96  --bmc1_k_induction                      false
% 1.53/0.96  --bmc1_non_equiv_states                 false
% 1.53/0.96  --bmc1_deadlock                         false
% 1.53/0.96  --bmc1_ucm                              false
% 1.53/0.96  --bmc1_add_unsat_core                   none
% 1.53/0.96  --bmc1_unsat_core_children              false
% 1.53/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.96  --bmc1_out_stat                         full
% 1.53/0.96  --bmc1_ground_init                      false
% 1.53/0.96  --bmc1_pre_inst_next_state              false
% 1.53/0.96  --bmc1_pre_inst_state                   false
% 1.53/0.96  --bmc1_pre_inst_reach_state             false
% 1.53/0.96  --bmc1_out_unsat_core                   false
% 1.53/0.96  --bmc1_aig_witness_out                  false
% 1.53/0.96  --bmc1_verbose                          false
% 1.53/0.96  --bmc1_dump_clauses_tptp                false
% 1.53/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.96  --bmc1_dump_file                        -
% 1.53/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.96  --bmc1_ucm_extend_mode                  1
% 1.53/0.96  --bmc1_ucm_init_mode                    2
% 1.53/0.96  --bmc1_ucm_cone_mode                    none
% 1.53/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.96  --bmc1_ucm_relax_model                  4
% 1.53/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.96  --bmc1_ucm_layered_model                none
% 1.53/0.96  --bmc1_ucm_max_lemma_size               10
% 1.53/0.96  
% 1.53/0.96  ------ AIG Options
% 1.53/0.96  
% 1.53/0.96  --aig_mode                              false
% 1.53/0.96  
% 1.53/0.96  ------ Instantiation Options
% 1.53/0.96  
% 1.53/0.96  --instantiation_flag                    true
% 1.53/0.96  --inst_sos_flag                         false
% 1.53/0.96  --inst_sos_phase                        true
% 1.53/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel_side                     num_symb
% 1.53/0.96  --inst_solver_per_active                1400
% 1.53/0.96  --inst_solver_calls_frac                1.
% 1.53/0.96  --inst_passive_queue_type               priority_queues
% 1.53/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.96  --inst_passive_queues_freq              [25;2]
% 1.53/0.96  --inst_dismatching                      true
% 1.53/0.96  --inst_eager_unprocessed_to_passive     true
% 1.53/0.96  --inst_prop_sim_given                   true
% 1.53/0.96  --inst_prop_sim_new                     false
% 1.53/0.96  --inst_subs_new                         false
% 1.53/0.96  --inst_eq_res_simp                      false
% 1.53/0.96  --inst_subs_given                       false
% 1.53/0.96  --inst_orphan_elimination               true
% 1.53/0.96  --inst_learning_loop_flag               true
% 1.53/0.96  --inst_learning_start                   3000
% 1.53/0.96  --inst_learning_factor                  2
% 1.53/0.96  --inst_start_prop_sim_after_learn       3
% 1.53/0.96  --inst_sel_renew                        solver
% 1.53/0.96  --inst_lit_activity_flag                true
% 1.53/0.96  --inst_restr_to_given                   false
% 1.53/0.96  --inst_activity_threshold               500
% 1.53/0.96  --inst_out_proof                        true
% 1.53/0.96  
% 1.53/0.96  ------ Resolution Options
% 1.53/0.96  
% 1.53/0.96  --resolution_flag                       true
% 1.53/0.96  --res_lit_sel                           adaptive
% 1.53/0.96  --res_lit_sel_side                      none
% 1.53/0.96  --res_ordering                          kbo
% 1.53/0.96  --res_to_prop_solver                    active
% 1.53/0.96  --res_prop_simpl_new                    false
% 1.53/0.96  --res_prop_simpl_given                  true
% 1.53/0.96  --res_passive_queue_type                priority_queues
% 1.53/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.96  --res_passive_queues_freq               [15;5]
% 1.53/0.96  --res_forward_subs                      full
% 1.53/0.96  --res_backward_subs                     full
% 1.53/0.96  --res_forward_subs_resolution           true
% 1.53/0.96  --res_backward_subs_resolution          true
% 1.53/0.96  --res_orphan_elimination                true
% 1.53/0.96  --res_time_limit                        2.
% 1.53/0.96  --res_out_proof                         true
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Options
% 1.53/0.96  
% 1.53/0.96  --superposition_flag                    true
% 1.53/0.96  --sup_passive_queue_type                priority_queues
% 1.53/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.96  --demod_completeness_check              fast
% 1.53/0.96  --demod_use_ground                      true
% 1.53/0.96  --sup_to_prop_solver                    passive
% 1.53/0.96  --sup_prop_simpl_new                    true
% 1.53/0.96  --sup_prop_simpl_given                  true
% 1.53/0.96  --sup_fun_splitting                     false
% 1.53/0.96  --sup_smt_interval                      50000
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Simplification Setup
% 1.53/0.96  
% 1.53/0.96  --sup_indices_passive                   []
% 1.53/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_full_bw                           [BwDemod]
% 1.53/0.96  --sup_immed_triv                        [TrivRules]
% 1.53/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_immed_bw_main                     []
% 1.53/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  
% 1.53/0.96  ------ Combination Options
% 1.53/0.96  
% 1.53/0.96  --comb_res_mult                         3
% 1.53/0.96  --comb_sup_mult                         2
% 1.53/0.96  --comb_inst_mult                        10
% 1.53/0.96  
% 1.53/0.96  ------ Debug Options
% 1.53/0.96  
% 1.53/0.96  --dbg_backtrace                         false
% 1.53/0.96  --dbg_dump_prop_clauses                 false
% 1.53/0.96  --dbg_dump_prop_clauses_file            -
% 1.53/0.96  --dbg_out_stat                          false
% 1.53/0.96  ------ Parsing...
% 1.53/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.53/0.96  ------ Proving...
% 1.53/0.96  ------ Problem Properties 
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  clauses                                 14
% 1.53/0.96  conjectures                             2
% 1.53/0.96  EPR                                     13
% 1.53/0.96  Horn                                    12
% 1.53/0.96  unary                                   4
% 1.53/0.96  binary                                  4
% 1.53/0.96  lits                                    34
% 1.53/0.96  lits eq                                 6
% 1.53/0.96  fd_pure                                 0
% 1.53/0.96  fd_pseudo                               0
% 1.53/0.96  fd_cond                                 1
% 1.53/0.96  fd_pseudo_cond                          3
% 1.53/0.96  AC symbols                              0
% 1.53/0.96  
% 1.53/0.96  ------ Schedule dynamic 5 is on 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  ------ 
% 1.53/0.96  Current options:
% 1.53/0.96  ------ 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options
% 1.53/0.96  
% 1.53/0.96  --out_options                           all
% 1.53/0.96  --tptp_safe_out                         true
% 1.53/0.96  --problem_path                          ""
% 1.53/0.96  --include_path                          ""
% 1.53/0.96  --clausifier                            res/vclausify_rel
% 1.53/0.96  --clausifier_options                    --mode clausify
% 1.53/0.96  --stdin                                 false
% 1.53/0.96  --stats_out                             all
% 1.53/0.96  
% 1.53/0.96  ------ General Options
% 1.53/0.96  
% 1.53/0.96  --fof                                   false
% 1.53/0.96  --time_out_real                         305.
% 1.53/0.96  --time_out_virtual                      -1.
% 1.53/0.96  --symbol_type_check                     false
% 1.53/0.96  --clausify_out                          false
% 1.53/0.96  --sig_cnt_out                           false
% 1.53/0.96  --trig_cnt_out                          false
% 1.53/0.96  --trig_cnt_out_tolerance                1.
% 1.53/0.96  --trig_cnt_out_sk_spl                   false
% 1.53/0.96  --abstr_cl_out                          false
% 1.53/0.96  
% 1.53/0.96  ------ Global Options
% 1.53/0.96  
% 1.53/0.96  --schedule                              default
% 1.53/0.96  --add_important_lit                     false
% 1.53/0.96  --prop_solver_per_cl                    1000
% 1.53/0.96  --min_unsat_core                        false
% 1.53/0.96  --soft_assumptions                      false
% 1.53/0.96  --soft_lemma_size                       3
% 1.53/0.96  --prop_impl_unit_size                   0
% 1.53/0.96  --prop_impl_unit                        []
% 1.53/0.96  --share_sel_clauses                     true
% 1.53/0.96  --reset_solvers                         false
% 1.53/0.96  --bc_imp_inh                            [conj_cone]
% 1.53/0.96  --conj_cone_tolerance                   3.
% 1.53/0.96  --extra_neg_conj                        none
% 1.53/0.96  --large_theory_mode                     true
% 1.53/0.96  --prolific_symb_bound                   200
% 1.53/0.96  --lt_threshold                          2000
% 1.53/0.96  --clause_weak_htbl                      true
% 1.53/0.96  --gc_record_bc_elim                     false
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing Options
% 1.53/0.96  
% 1.53/0.96  --preprocessing_flag                    true
% 1.53/0.96  --time_out_prep_mult                    0.1
% 1.53/0.96  --splitting_mode                        input
% 1.53/0.96  --splitting_grd                         true
% 1.53/0.96  --splitting_cvd                         false
% 1.53/0.96  --splitting_cvd_svl                     false
% 1.53/0.96  --splitting_nvd                         32
% 1.53/0.96  --sub_typing                            true
% 1.53/0.96  --prep_gs_sim                           true
% 1.53/0.96  --prep_unflatten                        true
% 1.53/0.96  --prep_res_sim                          true
% 1.53/0.96  --prep_upred                            true
% 1.53/0.96  --prep_sem_filter                       exhaustive
% 1.53/0.96  --prep_sem_filter_out                   false
% 1.53/0.96  --pred_elim                             true
% 1.53/0.96  --res_sim_input                         true
% 1.53/0.96  --eq_ax_congr_red                       true
% 1.53/0.96  --pure_diseq_elim                       true
% 1.53/0.96  --brand_transform                       false
% 1.53/0.96  --non_eq_to_eq                          false
% 1.53/0.96  --prep_def_merge                        true
% 1.53/0.96  --prep_def_merge_prop_impl              false
% 1.53/0.96  --prep_def_merge_mbd                    true
% 1.53/0.96  --prep_def_merge_tr_red                 false
% 1.53/0.96  --prep_def_merge_tr_cl                  false
% 1.53/0.96  --smt_preprocessing                     true
% 1.53/0.96  --smt_ac_axioms                         fast
% 1.53/0.96  --preprocessed_out                      false
% 1.53/0.96  --preprocessed_stats                    false
% 1.53/0.96  
% 1.53/0.96  ------ Abstraction refinement Options
% 1.53/0.96  
% 1.53/0.96  --abstr_ref                             []
% 1.53/0.96  --abstr_ref_prep                        false
% 1.53/0.96  --abstr_ref_until_sat                   false
% 1.53/0.96  --abstr_ref_sig_restrict                funpre
% 1.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.96  --abstr_ref_under                       []
% 1.53/0.96  
% 1.53/0.96  ------ SAT Options
% 1.53/0.96  
% 1.53/0.96  --sat_mode                              false
% 1.53/0.96  --sat_fm_restart_options                ""
% 1.53/0.97  --sat_gr_def                            false
% 1.53/0.97  --sat_epr_types                         true
% 1.53/0.97  --sat_non_cyclic_types                  false
% 1.53/0.97  --sat_finite_models                     false
% 1.53/0.97  --sat_fm_lemmas                         false
% 1.53/0.97  --sat_fm_prep                           false
% 1.53/0.97  --sat_fm_uc_incr                        true
% 1.53/0.97  --sat_out_model                         small
% 1.53/0.97  --sat_out_clauses                       false
% 1.53/0.97  
% 1.53/0.97  ------ QBF Options
% 1.53/0.97  
% 1.53/0.97  --qbf_mode                              false
% 1.53/0.97  --qbf_elim_univ                         false
% 1.53/0.97  --qbf_dom_inst                          none
% 1.53/0.97  --qbf_dom_pre_inst                      false
% 1.53/0.97  --qbf_sk_in                             false
% 1.53/0.97  --qbf_pred_elim                         true
% 1.53/0.97  --qbf_split                             512
% 1.53/0.97  
% 1.53/0.97  ------ BMC1 Options
% 1.53/0.97  
% 1.53/0.97  --bmc1_incremental                      false
% 1.53/0.97  --bmc1_axioms                           reachable_all
% 1.53/0.97  --bmc1_min_bound                        0
% 1.53/0.97  --bmc1_max_bound                        -1
% 1.53/0.97  --bmc1_max_bound_default                -1
% 1.53/0.97  --bmc1_symbol_reachability              true
% 1.53/0.97  --bmc1_property_lemmas                  false
% 1.53/0.97  --bmc1_k_induction                      false
% 1.53/0.97  --bmc1_non_equiv_states                 false
% 1.53/0.97  --bmc1_deadlock                         false
% 1.53/0.97  --bmc1_ucm                              false
% 1.53/0.97  --bmc1_add_unsat_core                   none
% 1.53/0.97  --bmc1_unsat_core_children              false
% 1.53/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.97  --bmc1_out_stat                         full
% 1.53/0.97  --bmc1_ground_init                      false
% 1.53/0.97  --bmc1_pre_inst_next_state              false
% 1.53/0.97  --bmc1_pre_inst_state                   false
% 1.53/0.97  --bmc1_pre_inst_reach_state             false
% 1.53/0.97  --bmc1_out_unsat_core                   false
% 1.53/0.97  --bmc1_aig_witness_out                  false
% 1.53/0.97  --bmc1_verbose                          false
% 1.53/0.97  --bmc1_dump_clauses_tptp                false
% 1.53/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.97  --bmc1_dump_file                        -
% 1.53/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.97  --bmc1_ucm_extend_mode                  1
% 1.53/0.97  --bmc1_ucm_init_mode                    2
% 1.53/0.97  --bmc1_ucm_cone_mode                    none
% 1.53/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.97  --bmc1_ucm_relax_model                  4
% 1.53/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.97  --bmc1_ucm_layered_model                none
% 1.53/0.97  --bmc1_ucm_max_lemma_size               10
% 1.53/0.97  
% 1.53/0.97  ------ AIG Options
% 1.53/0.97  
% 1.53/0.97  --aig_mode                              false
% 1.53/0.97  
% 1.53/0.97  ------ Instantiation Options
% 1.53/0.97  
% 1.53/0.97  --instantiation_flag                    true
% 1.53/0.97  --inst_sos_flag                         false
% 1.53/0.97  --inst_sos_phase                        true
% 1.53/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel_side                     none
% 1.53/0.97  --inst_solver_per_active                1400
% 1.53/0.97  --inst_solver_calls_frac                1.
% 1.53/0.97  --inst_passive_queue_type               priority_queues
% 1.53/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.97  --inst_passive_queues_freq              [25;2]
% 1.53/0.97  --inst_dismatching                      true
% 1.53/0.97  --inst_eager_unprocessed_to_passive     true
% 1.53/0.97  --inst_prop_sim_given                   true
% 1.53/0.97  --inst_prop_sim_new                     false
% 1.53/0.97  --inst_subs_new                         false
% 1.53/0.97  --inst_eq_res_simp                      false
% 1.53/0.97  --inst_subs_given                       false
% 1.53/0.97  --inst_orphan_elimination               true
% 1.53/0.97  --inst_learning_loop_flag               true
% 1.53/0.97  --inst_learning_start                   3000
% 1.53/0.97  --inst_learning_factor                  2
% 1.53/0.97  --inst_start_prop_sim_after_learn       3
% 1.53/0.97  --inst_sel_renew                        solver
% 1.53/0.97  --inst_lit_activity_flag                true
% 1.53/0.97  --inst_restr_to_given                   false
% 1.53/0.97  --inst_activity_threshold               500
% 1.53/0.97  --inst_out_proof                        true
% 1.53/0.97  
% 1.53/0.97  ------ Resolution Options
% 1.53/0.97  
% 1.53/0.97  --resolution_flag                       false
% 1.53/0.97  --res_lit_sel                           adaptive
% 1.53/0.97  --res_lit_sel_side                      none
% 1.53/0.97  --res_ordering                          kbo
% 1.53/0.97  --res_to_prop_solver                    active
% 1.53/0.97  --res_prop_simpl_new                    false
% 1.53/0.97  --res_prop_simpl_given                  true
% 1.53/0.97  --res_passive_queue_type                priority_queues
% 1.53/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.97  --res_passive_queues_freq               [15;5]
% 1.53/0.97  --res_forward_subs                      full
% 1.53/0.97  --res_backward_subs                     full
% 1.53/0.97  --res_forward_subs_resolution           true
% 1.53/0.97  --res_backward_subs_resolution          true
% 1.53/0.97  --res_orphan_elimination                true
% 1.53/0.97  --res_time_limit                        2.
% 1.53/0.97  --res_out_proof                         true
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Options
% 1.53/0.97  
% 1.53/0.97  --superposition_flag                    true
% 1.53/0.97  --sup_passive_queue_type                priority_queues
% 1.53/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.97  --demod_completeness_check              fast
% 1.53/0.97  --demod_use_ground                      true
% 1.53/0.97  --sup_to_prop_solver                    passive
% 1.53/0.97  --sup_prop_simpl_new                    true
% 1.53/0.97  --sup_prop_simpl_given                  true
% 1.53/0.97  --sup_fun_splitting                     false
% 1.53/0.97  --sup_smt_interval                      50000
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Simplification Setup
% 1.53/0.97  
% 1.53/0.97  --sup_indices_passive                   []
% 1.53/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_full_bw                           [BwDemod]
% 1.53/0.97  --sup_immed_triv                        [TrivRules]
% 1.53/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_immed_bw_main                     []
% 1.53/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  
% 1.53/0.97  ------ Combination Options
% 1.53/0.97  
% 1.53/0.97  --comb_res_mult                         3
% 1.53/0.97  --comb_sup_mult                         2
% 1.53/0.97  --comb_inst_mult                        10
% 1.53/0.97  
% 1.53/0.97  ------ Debug Options
% 1.53/0.97  
% 1.53/0.97  --dbg_backtrace                         false
% 1.53/0.97  --dbg_dump_prop_clauses                 false
% 1.53/0.97  --dbg_dump_prop_clauses_file            -
% 1.53/0.97  --dbg_out_stat                          false
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  ------ Proving...
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  % SZS status Theorem for theBenchmark.p
% 1.53/0.97  
% 1.53/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.53/0.97  
% 1.53/0.97  fof(f10,conjecture,(
% 1.53/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f11,negated_conjecture,(
% 1.53/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.53/0.97    inference(negated_conjecture,[],[f10])).
% 1.53/0.97  
% 1.53/0.97  fof(f24,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f11])).
% 1.53/0.97  
% 1.53/0.97  fof(f25,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f24])).
% 1.53/0.97  
% 1.53/0.97  fof(f31,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(nnf_transformation,[],[f25])).
% 1.53/0.97  
% 1.53/0.97  fof(f32,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f31])).
% 1.53/0.97  
% 1.53/0.97  fof(f36,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f35,plain,(
% 1.53/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f34,plain,(
% 1.53/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f33,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f37,plain,(
% 1.53/0.97    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.53/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).
% 1.53/0.97  
% 1.53/0.97  fof(f59,plain,(
% 1.53/0.97    m2_orders_2(sK2,sK0,sK1)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f60,plain,(
% 1.53/0.97    m2_orders_2(sK3,sK0,sK1)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f9,axiom,(
% 1.53/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f22,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f9])).
% 1.53/0.97  
% 1.53/0.97  fof(f23,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f22])).
% 1.53/0.97  
% 1.53/0.97  fof(f30,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(nnf_transformation,[],[f23])).
% 1.53/0.97  
% 1.53/0.97  fof(f52,plain,(
% 1.53/0.97    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f30])).
% 1.53/0.97  
% 1.53/0.97  fof(f58,plain,(
% 1.53/0.97    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f57,plain,(
% 1.53/0.97    l1_orders_2(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f53,plain,(
% 1.53/0.97    ~v2_struct_0(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f54,plain,(
% 1.53/0.97    v3_orders_2(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f55,plain,(
% 1.53/0.97    v4_orders_2(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f56,plain,(
% 1.53/0.97    v5_orders_2(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f1,axiom,(
% 1.53/0.97    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f26,plain,(
% 1.53/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.53/0.97    inference(nnf_transformation,[],[f1])).
% 1.53/0.97  
% 1.53/0.97  fof(f27,plain,(
% 1.53/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.53/0.97    inference(flattening,[],[f26])).
% 1.53/0.97  
% 1.53/0.97  fof(f39,plain,(
% 1.53/0.97    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f27])).
% 1.53/0.97  
% 1.53/0.97  fof(f63,plain,(
% 1.53/0.97    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.53/0.97    inference(equality_resolution,[],[f39])).
% 1.53/0.97  
% 1.53/0.97  fof(f61,plain,(
% 1.53/0.97    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f5,axiom,(
% 1.53/0.97    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f12,plain,(
% 1.53/0.97    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.97    inference(pure_predicate_removal,[],[f5])).
% 1.53/0.97  
% 1.53/0.97  fof(f14,plain,(
% 1.53/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f12])).
% 1.53/0.97  
% 1.53/0.97  fof(f15,plain,(
% 1.53/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f14])).
% 1.53/0.97  
% 1.53/0.97  fof(f46,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f15])).
% 1.53/0.97  
% 1.53/0.97  fof(f6,axiom,(
% 1.53/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f16,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f6])).
% 1.53/0.97  
% 1.53/0.97  fof(f17,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f16])).
% 1.53/0.97  
% 1.53/0.97  fof(f47,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f17])).
% 1.53/0.97  
% 1.53/0.97  fof(f51,plain,(
% 1.53/0.97    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f30])).
% 1.53/0.97  
% 1.53/0.97  fof(f40,plain,(
% 1.53/0.97    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f27])).
% 1.53/0.97  
% 1.53/0.97  fof(f62,plain,(
% 1.53/0.97    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.53/0.97    inference(cnf_transformation,[],[f37])).
% 1.53/0.97  
% 1.53/0.97  fof(f3,axiom,(
% 1.53/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f44,plain,(
% 1.53/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f3])).
% 1.53/0.97  
% 1.53/0.97  fof(f4,axiom,(
% 1.53/0.97    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f13,plain,(
% 1.53/0.97    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.53/0.97    inference(ennf_transformation,[],[f4])).
% 1.53/0.97  
% 1.53/0.97  fof(f45,plain,(
% 1.53/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f13])).
% 1.53/0.97  
% 1.53/0.97  fof(f8,axiom,(
% 1.53/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f20,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f8])).
% 1.53/0.97  
% 1.53/0.97  fof(f21,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f20])).
% 1.53/0.97  
% 1.53/0.97  fof(f50,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f21])).
% 1.53/0.97  
% 1.53/0.97  fof(f2,axiom,(
% 1.53/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f28,plain,(
% 1.53/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.97    inference(nnf_transformation,[],[f2])).
% 1.53/0.97  
% 1.53/0.97  fof(f29,plain,(
% 1.53/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.97    inference(flattening,[],[f28])).
% 1.53/0.97  
% 1.53/0.97  fof(f43,plain,(
% 1.53/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f29])).
% 1.53/0.97  
% 1.53/0.97  fof(f7,axiom,(
% 1.53/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f18,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f7])).
% 1.53/0.97  
% 1.53/0.97  fof(f19,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f18])).
% 1.53/0.97  
% 1.53/0.97  fof(f48,plain,(
% 1.53/0.97    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f19])).
% 1.53/0.97  
% 1.53/0.97  fof(f38,plain,(
% 1.53/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f27])).
% 1.53/0.97  
% 1.53/0.97  fof(f41,plain,(
% 1.53/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.53/0.97    inference(cnf_transformation,[],[f29])).
% 1.53/0.97  
% 1.53/0.97  fof(f65,plain,(
% 1.53/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.97    inference(equality_resolution,[],[f41])).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1059,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | m2_orders_2(X3,X4,X5)
% 1.53/0.97      | X3 != X0
% 1.53/0.97      | X4 != X1
% 1.53/0.97      | X5 != X2 ),
% 1.53/0.97      theory(equality) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1444,plain,
% 1.53/0.97      ( m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | X2 != sK1
% 1.53/0.97      | X0 != sK3
% 1.53/0.97      | X1 != sK0 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1059]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1501,plain,
% 1.53/0.97      ( m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | X0 != sK3
% 1.53/0.97      | X1 != sK0
% 1.53/0.97      | sK1 != sK1 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1444]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2138,plain,
% 1.53/0.97      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | m2_orders_2(k1_xboole_0,X0,sK1)
% 1.53/0.97      | X0 != sK0
% 1.53/0.97      | sK1 != sK1
% 1.53/0.97      | k1_xboole_0 != sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1501]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2140,plain,
% 1.53/0.97      ( ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | m2_orders_2(k1_xboole_0,sK0,sK1)
% 1.53/0.97      | sK1 != sK1
% 1.53/0.97      | sK0 != sK0
% 1.53/0.97      | k1_xboole_0 != sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_2138]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_18,negated_conjecture,
% 1.53/0.97      ( m2_orders_2(sK2,sK0,sK1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1321,plain,
% 1.53/0.97      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_17,negated_conjecture,
% 1.53/0.97      ( m2_orders_2(sK3,sK0,sK1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1322,plain,
% 1.53/0.97      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_13,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,X3)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,X3)
% 1.53/0.97      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X0 = X2 ),
% 1.53/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_19,negated_conjecture,
% 1.53/0.97      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 1.53/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_510,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,X3)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,X3)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK1 != X3 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_511,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,sK1)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_510]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_20,negated_conjecture,
% 1.53/0.97      ( l1_orders_2(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f57]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_721,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,sK1)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_511,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_722,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0)
% 1.53/0.97      | X0 = X1
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_721]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_24,negated_conjecture,
% 1.53/0.97      ( ~ v2_struct_0(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_23,negated_conjecture,
% 1.53/0.97      ( v3_orders_2(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_22,negated_conjecture,
% 1.53/0.97      ( v4_orders_2(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_21,negated_conjecture,
% 1.53/0.97      ( v5_orders_2(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f56]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_726,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | X0 = X1
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_722,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_974,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | X0 = X1 ),
% 1.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_726]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1312,plain,
% 1.53/0.97      ( X0 = X1
% 1.53/0.97      | m1_orders_2(X0,sK0,X1) = iProver_top
% 1.53/0.97      | m1_orders_2(X1,sK0,X0) = iProver_top
% 1.53/0.97      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.53/0.97      | m2_orders_2(X1,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1775,plain,
% 1.53/0.97      ( sK3 = X0
% 1.53/0.97      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 1.53/0.97      | m1_orders_2(sK3,sK0,X0) = iProver_top
% 1.53/0.97      | m2_orders_2(X0,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1322,c_1312]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2082,plain,
% 1.53/0.97      ( sK3 = sK2
% 1.53/0.97      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1321,c_1775]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_31,plain,
% 1.53/0.97      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_32,plain,
% 1.53/0.97      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1,plain,
% 1.53/0.97      ( ~ r2_xboole_0(X0,X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f63]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_16,negated_conjecture,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.53/0.97      inference(cnf_transformation,[],[f61]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_179,plain,
% 1.53/0.97      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 1.53/0.97      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_180,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 1.53/0.97      inference(renaming,[status(thm)],[c_179]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_391,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_180]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_392,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_391]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_393,plain,
% 1.53/0.97      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1538,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,sK3)
% 1.53/0.97      | m1_orders_2(sK3,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | X0 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_974]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1699,plain,
% 1.53/0.97      ( m1_orders_2(sK3,sK0,sK2)
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(sK2,sK0,sK1)
% 1.53/0.97      | sK2 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1538]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1700,plain,
% 1.53/0.97      ( sK2 = sK3
% 1.53/0.97      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3) = iProver_top
% 1.53/0.97      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.53/0.97      | m2_orders_2(sK2,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2091,plain,
% 1.53/0.97      ( m1_orders_2(sK3,sK0,sK2) = iProver_top
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_2082,c_31,c_32,c_393,c_1700]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_8,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_441,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK1 != X2 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_442,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_441]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_781,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_442,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_782,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0)
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_781]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_786,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_782,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_9,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | r1_tarski(X0,X2)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_844,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | r1_tarski(X0,X2)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_845,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | r1_tarski(X0,X1)
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_844]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_847,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | r1_tarski(X0,X1) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_845,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_921,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m2_orders_2(X2,sK0,sK1)
% 1.53/0.97      | r1_tarski(X0,X1)
% 1.53/0.97      | X1 != X2
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_786,c_847]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_922,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | r1_tarski(X0,X1) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_921]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1316,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 1.53/0.97      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 1.53/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1520,plain,
% 1.53/0.97      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 1.53/0.97      | r1_tarski(X0,sK2) = iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1321,c_1316]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2097,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 1.53/0.97      | r1_tarski(sK3,sK2) = iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_2091,c_1520]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2098,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) ),
% 1.53/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2097]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_14,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,X3)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,X3)
% 1.53/0.97      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X0 = X2 ),
% 1.53/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_471,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,X3)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,X3)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK1 != X3 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_472,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,sK1)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_471]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_751,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_2(X2,X1,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ m2_orders_2(X2,X1,sK1)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | X2 = X0
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_472,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_752,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0)
% 1.53/0.97      | X0 = X1
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_751]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_756,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | X0 = X1
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_752,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_970,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X1)
% 1.53/0.97      | ~ m1_orders_2(X1,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ m2_orders_2(X1,sK0,sK1)
% 1.53/0.97      | X0 = X1 ),
% 1.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_756]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1313,plain,
% 1.53/0.97      ( X0 = X1
% 1.53/0.97      | m1_orders_2(X0,sK0,X1) != iProver_top
% 1.53/0.97      | m1_orders_2(X1,sK0,X0) != iProver_top
% 1.53/0.97      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.53/0.97      | m2_orders_2(X1,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1650,plain,
% 1.53/0.97      ( sK3 = X0
% 1.53/0.97      | m1_orders_2(X0,sK0,sK3) != iProver_top
% 1.53/0.97      | m1_orders_2(sK3,sK0,X0) != iProver_top
% 1.53/0.97      | m2_orders_2(X0,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1322,c_1313]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1980,plain,
% 1.53/0.97      ( sK3 = sK2
% 1.53/0.97      | m1_orders_2(sK3,sK0,sK2) != iProver_top
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1321,c_1650]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_0,plain,
% 1.53/0.97      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.53/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_15,negated_conjecture,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.53/0.97      inference(cnf_transformation,[],[f62]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_177,plain,
% 1.53/0.97      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 1.53/0.97      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_178,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 1.53/0.97      inference(renaming,[status(thm)],[c_177]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_368,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | ~ r1_tarski(X0,X1)
% 1.53/0.97      | X1 = X0
% 1.53/0.97      | sK3 != X1
% 1.53/0.97      | sK2 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_178]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_369,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_368]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_370,plain,
% 1.53/0.97      ( sK3 = sK2
% 1.53/0.97      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.53/0.97      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1437,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | r1_tarski(sK2,sK3) ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_922]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1438,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 1.53/0.97      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 1.53/0.97      | r1_tarski(sK2,sK3) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_1437]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2043,plain,
% 1.53/0.97      ( sK3 = sK2 | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_1980,c_32,c_370,c_1438]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2045,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK2,sK0,sK3) | sK3 = sK2 ),
% 1.53/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2043]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_6,plain,
% 1.53/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1323,plain,
% 1.53/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_7,plain,
% 1.53/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_12,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_325,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ r1_tarski(X3,X4)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | X0 != X3
% 1.53/0.97      | k1_funct_1(X2,u1_struct_0(X1)) != X4 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_326,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_325]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_411,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK1 != X2 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_326,c_19]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_412,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_411]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_802,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,X1,sK1)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_412,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_803,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0)
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_802]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_807,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_803,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_966,plain,
% 1.53/0.97      ( ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
% 1.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_807]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1314,plain,
% 1.53/0.97      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 1.53/0.97      | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
% 1.53/0.97      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1801,plain,
% 1.53/0.97      ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 1.53/0.97      inference(superposition,[status(thm)],[c_1323,c_1314]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1802,plain,
% 1.53/0.97      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
% 1.53/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1801]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1060,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.53/0.97      | m1_orders_2(X3,X4,X5)
% 1.53/0.97      | X3 != X0
% 1.53/0.97      | X4 != X1
% 1.53/0.97      | X5 != X2 ),
% 1.53/0.97      theory(equality) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1454,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,X2)
% 1.53/0.97      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | X2 != sK3
% 1.53/0.97      | X1 != sK0
% 1.53/0.97      | X0 != sK2 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1060]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1553,plain,
% 1.53/0.97      ( m1_orders_2(X0,X1,sK3)
% 1.53/0.97      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | X1 != sK0
% 1.53/0.97      | X0 != sK2
% 1.53/0.97      | sK3 != sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1454]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1751,plain,
% 1.53/0.97      ( m1_orders_2(sK3,X0,sK3)
% 1.53/0.97      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | X0 != sK0
% 1.53/0.97      | sK3 != sK3
% 1.53/0.97      | sK3 != sK2 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1553]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1753,plain,
% 1.53/0.97      ( m1_orders_2(sK3,sK0,sK3)
% 1.53/0.97      | ~ m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | sK3 != sK3
% 1.53/0.97      | sK3 != sK2
% 1.53/0.97      | sK0 != sK0 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1751]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_3,plain,
% 1.53/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.53/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1548,plain,
% 1.53/0.97      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1724,plain,
% 1.53/0.97      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1548]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1055,plain,( X0 = X0 ),theory(equality) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1554,plain,
% 1.53/0.97      ( sK3 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1502,plain,
% 1.53/0.97      ( sK1 = sK1 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_11,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X0)
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | ~ l1_orders_2(X1)
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_823,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,X1,X0)
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ v3_orders_2(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | ~ v5_orders_2(X1)
% 1.53/0.97      | sK0 != X1
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_824,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X0)
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | ~ v3_orders_2(sK0)
% 1.53/0.97      | ~ v4_orders_2(sK0)
% 1.53/0.97      | ~ v5_orders_2(sK0)
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_823]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_828,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X0)
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_824,c_24,c_23,c_22,c_21]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_894,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0))
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(resolution,[status(thm)],[c_786,c_828]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_962,plain,
% 1.53/0.97      ( ~ m1_orders_2(X0,sK0,X0)
% 1.53/0.97      | ~ m2_orders_2(X0,sK0,sK1)
% 1.53/0.97      | k1_xboole_0 = X0 ),
% 1.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_894]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1431,plain,
% 1.53/0.97      ( ~ m1_orders_2(sK3,sK0,sK3)
% 1.53/0.97      | ~ m2_orders_2(sK3,sK0,sK1)
% 1.53/0.97      | k1_xboole_0 = sK3 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_962]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2,plain,
% 1.53/0.97      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_381,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3)
% 1.53/0.97      | r1_tarski(X0,X1)
% 1.53/0.97      | sK3 != X1
% 1.53/0.97      | sK2 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_180]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_382,plain,
% 1.53/0.97      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_381]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_67,plain,
% 1.53/0.97      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_5,plain,
% 1.53/0.97      ( r1_tarski(X0,X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f65]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_63,plain,
% 1.53/0.97      ( r1_tarski(sK0,sK0) ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(contradiction,plain,
% 1.53/0.97      ( $false ),
% 1.53/0.97      inference(minisat,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_2140,c_2098,c_2045,c_1802,c_1753,c_1724,c_1554,c_1502,
% 1.53/0.97                 c_1431,c_392,c_382,c_67,c_63,c_17]) ).
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.53/0.97  
% 1.53/0.97  ------                               Statistics
% 1.53/0.97  
% 1.53/0.97  ------ General
% 1.53/0.97  
% 1.53/0.97  abstr_ref_over_cycles:                  0
% 1.53/0.97  abstr_ref_under_cycles:                 0
% 1.53/0.97  gc_basic_clause_elim:                   0
% 1.53/0.97  forced_gc_time:                         0
% 1.53/0.97  parsing_time:                           0.009
% 1.53/0.97  unif_index_cands_time:                  0.
% 1.53/0.97  unif_index_add_time:                    0.
% 1.53/0.97  orderings_time:                         0.
% 1.53/0.97  out_proof_time:                         0.015
% 1.53/0.97  total_time:                             0.106
% 1.53/0.97  num_of_symbols:                         52
% 1.53/0.97  num_of_terms:                           1138
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing
% 1.53/0.97  
% 1.53/0.97  num_of_splits:                          0
% 1.53/0.97  num_of_split_atoms:                     0
% 1.53/0.97  num_of_reused_defs:                     0
% 1.53/0.97  num_eq_ax_congr_red:                    3
% 1.53/0.97  num_of_sem_filtered_clauses:            1
% 1.53/0.97  num_of_subtypes:                        0
% 1.53/0.97  monotx_restored_types:                  0
% 1.53/0.97  sat_num_of_epr_types:                   0
% 1.53/0.97  sat_num_of_non_cyclic_types:            0
% 1.53/0.97  sat_guarded_non_collapsed_types:        0
% 1.53/0.97  num_pure_diseq_elim:                    0
% 1.53/0.97  simp_replaced_by:                       0
% 1.53/0.97  res_preprocessed:                       81
% 1.53/0.97  prep_upred:                             0
% 1.53/0.97  prep_unflattend:                        24
% 1.53/0.97  smt_new_axioms:                         0
% 1.53/0.97  pred_elim_cands:                        3
% 1.53/0.97  pred_elim:                              9
% 1.53/0.97  pred_elim_cl:                           10
% 1.53/0.97  pred_elim_cycles:                       12
% 1.53/0.97  merged_defs:                            2
% 1.53/0.97  merged_defs_ncl:                        0
% 1.53/0.97  bin_hyper_res:                          2
% 1.53/0.97  prep_cycles:                            4
% 1.53/0.97  pred_elim_time:                         0.013
% 1.53/0.97  splitting_time:                         0.
% 1.53/0.97  sem_filter_time:                        0.
% 1.53/0.97  monotx_time:                            0.
% 1.53/0.97  subtype_inf_time:                       0.
% 1.53/0.97  
% 1.53/0.97  ------ Problem properties
% 1.53/0.97  
% 1.53/0.97  clauses:                                14
% 1.53/0.97  conjectures:                            2
% 1.53/0.97  epr:                                    13
% 1.53/0.97  horn:                                   12
% 1.53/0.97  ground:                                 6
% 1.53/0.97  unary:                                  4
% 1.53/0.97  binary:                                 4
% 1.53/0.97  lits:                                   34
% 1.53/0.97  lits_eq:                                6
% 1.53/0.97  fd_pure:                                0
% 1.53/0.97  fd_pseudo:                              0
% 1.53/0.97  fd_cond:                                1
% 1.53/0.97  fd_pseudo_cond:                         3
% 1.53/0.97  ac_symbols:                             0
% 1.53/0.97  
% 1.53/0.97  ------ Propositional Solver
% 1.53/0.97  
% 1.53/0.97  prop_solver_calls:                      25
% 1.53/0.97  prop_fast_solver_calls:                 708
% 1.53/0.97  smt_solver_calls:                       0
% 1.53/0.97  smt_fast_solver_calls:                  0
% 1.53/0.97  prop_num_of_clauses:                    546
% 1.53/0.97  prop_preprocess_simplified:             2565
% 1.53/0.97  prop_fo_subsumed:                       31
% 1.53/0.97  prop_solver_time:                       0.
% 1.53/0.97  smt_solver_time:                        0.
% 1.53/0.97  smt_fast_solver_time:                   0.
% 1.53/0.97  prop_fast_solver_time:                  0.
% 1.53/0.97  prop_unsat_core_time:                   0.
% 1.53/0.97  
% 1.53/0.97  ------ QBF
% 1.53/0.97  
% 1.53/0.97  qbf_q_res:                              0
% 1.53/0.97  qbf_num_tautologies:                    0
% 1.53/0.97  qbf_prep_cycles:                        0
% 1.53/0.97  
% 1.53/0.97  ------ BMC1
% 1.53/0.97  
% 1.53/0.97  bmc1_current_bound:                     -1
% 1.53/0.97  bmc1_last_solved_bound:                 -1
% 1.53/0.97  bmc1_unsat_core_size:                   -1
% 1.53/0.97  bmc1_unsat_core_parents_size:           -1
% 1.53/0.97  bmc1_merge_next_fun:                    0
% 1.53/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.53/0.97  
% 1.53/0.97  ------ Instantiation
% 1.53/0.97  
% 1.53/0.97  inst_num_of_clauses:                    133
% 1.53/0.97  inst_num_in_passive:                    3
% 1.53/0.97  inst_num_in_active:                     94
% 1.53/0.97  inst_num_in_unprocessed:                36
% 1.53/0.97  inst_num_of_loops:                      100
% 1.53/0.97  inst_num_of_learning_restarts:          0
% 1.53/0.97  inst_num_moves_active_passive:          4
% 1.53/0.97  inst_lit_activity:                      0
% 1.53/0.97  inst_lit_activity_moves:                0
% 1.53/0.97  inst_num_tautologies:                   0
% 1.53/0.97  inst_num_prop_implied:                  0
% 1.53/0.97  inst_num_existing_simplified:           0
% 1.53/0.97  inst_num_eq_res_simplified:             0
% 1.53/0.97  inst_num_child_elim:                    0
% 1.53/0.97  inst_num_of_dismatching_blockings:      10
% 1.53/0.97  inst_num_of_non_proper_insts:           144
% 1.53/0.97  inst_num_of_duplicates:                 0
% 1.53/0.97  inst_inst_num_from_inst_to_res:         0
% 1.53/0.97  inst_dismatching_checking_time:         0.
% 1.53/0.97  
% 1.53/0.97  ------ Resolution
% 1.53/0.97  
% 1.53/0.97  res_num_of_clauses:                     0
% 1.53/0.97  res_num_in_passive:                     0
% 1.53/0.97  res_num_in_active:                      0
% 1.53/0.97  res_num_of_loops:                       85
% 1.53/0.97  res_forward_subset_subsumed:            22
% 1.53/0.97  res_backward_subset_subsumed:           0
% 1.53/0.97  res_forward_subsumed:                   0
% 1.53/0.97  res_backward_subsumed:                  0
% 1.53/0.97  res_forward_subsumption_resolution:     0
% 1.53/0.97  res_backward_subsumption_resolution:    0
% 1.53/0.97  res_clause_to_clause_subsumption:       65
% 1.53/0.97  res_orphan_elimination:                 0
% 1.53/0.97  res_tautology_del:                      12
% 1.53/0.97  res_num_eq_res_simplified:              4
% 1.53/0.97  res_num_sel_changes:                    0
% 1.53/0.97  res_moves_from_active_to_pass:          0
% 1.53/0.97  
% 1.53/0.97  ------ Superposition
% 1.53/0.97  
% 1.53/0.97  sup_time_total:                         0.
% 1.53/0.97  sup_time_generating:                    0.
% 1.53/0.97  sup_time_sim_full:                      0.
% 1.53/0.97  sup_time_sim_immed:                     0.
% 1.53/0.97  
% 1.53/0.97  sup_num_of_clauses:                     25
% 1.53/0.97  sup_num_in_active:                      19
% 1.53/0.97  sup_num_in_passive:                     6
% 1.53/0.97  sup_num_of_loops:                       19
% 1.53/0.97  sup_fw_superposition:                   16
% 1.53/0.97  sup_bw_superposition:                   3
% 1.53/0.97  sup_immediate_simplified:               0
% 1.53/0.97  sup_given_eliminated:                   0
% 1.53/0.97  comparisons_done:                       0
% 1.53/0.97  comparisons_avoided:                    0
% 1.53/0.97  
% 1.53/0.97  ------ Simplifications
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  sim_fw_subset_subsumed:                 0
% 1.53/0.97  sim_bw_subset_subsumed:                 1
% 1.53/0.97  sim_fw_subsumed:                        0
% 1.53/0.97  sim_bw_subsumed:                        0
% 1.53/0.97  sim_fw_subsumption_res:                 0
% 1.53/0.97  sim_bw_subsumption_res:                 0
% 1.53/0.97  sim_tautology_del:                      0
% 1.53/0.97  sim_eq_tautology_del:                   5
% 1.53/0.97  sim_eq_res_simp:                        0
% 1.53/0.97  sim_fw_demodulated:                     0
% 1.53/0.97  sim_bw_demodulated:                     0
% 1.53/0.97  sim_light_normalised:                   0
% 1.53/0.97  sim_joinable_taut:                      0
% 1.53/0.97  sim_joinable_simp:                      0
% 1.53/0.97  sim_ac_normalised:                      0
% 1.53/0.97  sim_smt_subsumption:                    0
% 1.53/0.97  
%------------------------------------------------------------------------------
