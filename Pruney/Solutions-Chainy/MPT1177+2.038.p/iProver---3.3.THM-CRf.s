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
% DateTime   : Thu Dec  3 12:12:55 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  199 (4569 expanded)
%              Number of clauses        :  131 ( 829 expanded)
%              Number of leaves         :   16 (1497 expanded)
%              Depth                    :   28
%              Number of atoms          :  987 (44334 expanded)
%              Number of equality atoms :  213 (1000 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f70,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f58,plain,(
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

fof(f69,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f60,plain,(
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

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f57,plain,(
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

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
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

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f72,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
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
    inference(ennf_transformation,[],[f12])).

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

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f59,plain,(
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

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1578,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_597,plain,
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

cnf(c_598,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_727,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_598,c_23])).

cnf(c_728,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_732,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_27,c_26,c_25,c_24])).

cnf(c_987,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_732])).

cnf(c_1568,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

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

cnf(c_829,plain,
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

cnf(c_830,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_834,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_27,c_26,c_25,c_24])).

cnf(c_835,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_834])).

cnf(c_1574,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_1833,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1574])).

cnf(c_4665,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_1833])).

cnf(c_34,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1724,plain,
    ( ~ m2_orders_2(sK2,sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1725,plain,
    ( m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1919,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1919])).

cnf(c_2259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_211,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_212,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_389,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_212])).

cnf(c_390,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1575,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_379,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_212])).

cnf(c_380,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_381,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_391,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2215,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2927,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_2928,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2927])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1579,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_528,plain,
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

cnf(c_529,plain,
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
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_769,plain,
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
    inference(resolution_lifted,[status(thm)],[c_529,c_23])).

cnf(c_770,plain,
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
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_774,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_27,c_26,c_25,c_24])).

cnf(c_983,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_774])).

cnf(c_1569,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_2756,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_1569])).

cnf(c_3200,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_2756])).

cnf(c_35,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2140,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(X0,sK0,sK2)
    | m1_orders_2(sK2,sK0,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_2710,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_2711,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2710])).

cnf(c_3209,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_34,c_35,c_391,c_2711])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_853,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_854,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_856,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_27,c_26,c_25,c_24])).

cnf(c_1573,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_1835,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1573])).

cnf(c_1986,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_1835])).

cnf(c_3215,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_1986])).

cnf(c_4065,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1575,c_381,c_391,c_2928,c_3215])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_489,plain,
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
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_490,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_799,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_490,c_23])).

cnf(c_800,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_804,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_27,c_26,c_25,c_24])).

cnf(c_979,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_804])).

cnf(c_1570,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_76,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_858,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_870,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_871,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_873,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_27,c_26,c_25,c_24])).

cnf(c_1572,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_1834,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1572])).

cnf(c_3493,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1570,c_76,c_858,c_1834,c_1835])).

cnf(c_3494,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3493])).

cnf(c_3501,plain,
    ( sK3 = X0
    | m1_orders_2(X0,sK0,sK3) != iProver_top
    | m1_orders_2(sK3,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_3494])).

cnf(c_4076,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4065,c_3501])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_209,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_210,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_366,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_210])).

cnf(c_367,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_368,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1721,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1722,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_1741,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1742,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_4508,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4076,c_35,c_368,c_381,c_391,c_1722,c_1742,c_2928,c_3215])).

cnf(c_4520,plain,
    ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4508,c_3209])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2265,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1574])).

cnf(c_4572,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_2265])).

cnf(c_4592,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4572,c_4520])).

cnf(c_4735,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4665,c_34,c_1725,c_2259,c_4592])).

cnf(c_4752,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4735,c_1578])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1582,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1580,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2200,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1580])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_567,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_568,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_748,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_568,c_23])).

cnf(c_749,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_748])).

cnf(c_753,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_749,c_27,c_26,c_25,c_24])).

cnf(c_922,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X1,X2)
    | X0 != X1
    | k1_funct_1(sK1,u1_struct_0(sK0)) != X2
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_753])).

cnf(c_923,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_1571,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_2913,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_1571])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4752,c_2913])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.36/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.02  
% 2.36/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/1.02  
% 2.36/1.02  ------  iProver source info
% 2.36/1.02  
% 2.36/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.36/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/1.02  git: non_committed_changes: false
% 2.36/1.02  git: last_make_outside_of_git: false
% 2.36/1.02  
% 2.36/1.02  ------ 
% 2.36/1.02  
% 2.36/1.02  ------ Input Options
% 2.36/1.02  
% 2.36/1.02  --out_options                           all
% 2.36/1.02  --tptp_safe_out                         true
% 2.36/1.02  --problem_path                          ""
% 2.36/1.02  --include_path                          ""
% 2.36/1.02  --clausifier                            res/vclausify_rel
% 2.36/1.02  --clausifier_options                    --mode clausify
% 2.36/1.02  --stdin                                 false
% 2.36/1.02  --stats_out                             all
% 2.36/1.02  
% 2.36/1.02  ------ General Options
% 2.36/1.02  
% 2.36/1.02  --fof                                   false
% 2.36/1.02  --time_out_real                         305.
% 2.36/1.02  --time_out_virtual                      -1.
% 2.36/1.02  --symbol_type_check                     false
% 2.36/1.02  --clausify_out                          false
% 2.36/1.02  --sig_cnt_out                           false
% 2.36/1.02  --trig_cnt_out                          false
% 2.36/1.02  --trig_cnt_out_tolerance                1.
% 2.36/1.02  --trig_cnt_out_sk_spl                   false
% 2.36/1.02  --abstr_cl_out                          false
% 2.36/1.02  
% 2.36/1.02  ------ Global Options
% 2.36/1.02  
% 2.36/1.02  --schedule                              default
% 2.36/1.02  --add_important_lit                     false
% 2.36/1.02  --prop_solver_per_cl                    1000
% 2.36/1.02  --min_unsat_core                        false
% 2.36/1.02  --soft_assumptions                      false
% 2.36/1.02  --soft_lemma_size                       3
% 2.36/1.02  --prop_impl_unit_size                   0
% 2.36/1.02  --prop_impl_unit                        []
% 2.36/1.02  --share_sel_clauses                     true
% 2.36/1.02  --reset_solvers                         false
% 2.36/1.02  --bc_imp_inh                            [conj_cone]
% 2.36/1.02  --conj_cone_tolerance                   3.
% 2.36/1.02  --extra_neg_conj                        none
% 2.36/1.02  --large_theory_mode                     true
% 2.36/1.02  --prolific_symb_bound                   200
% 2.36/1.02  --lt_threshold                          2000
% 2.36/1.02  --clause_weak_htbl                      true
% 2.36/1.02  --gc_record_bc_elim                     false
% 2.36/1.02  
% 2.36/1.02  ------ Preprocessing Options
% 2.36/1.02  
% 2.36/1.02  --preprocessing_flag                    true
% 2.36/1.02  --time_out_prep_mult                    0.1
% 2.36/1.02  --splitting_mode                        input
% 2.36/1.02  --splitting_grd                         true
% 2.36/1.02  --splitting_cvd                         false
% 2.36/1.02  --splitting_cvd_svl                     false
% 2.36/1.02  --splitting_nvd                         32
% 2.36/1.02  --sub_typing                            true
% 2.36/1.02  --prep_gs_sim                           true
% 2.36/1.02  --prep_unflatten                        true
% 2.36/1.02  --prep_res_sim                          true
% 2.36/1.02  --prep_upred                            true
% 2.36/1.02  --prep_sem_filter                       exhaustive
% 2.36/1.02  --prep_sem_filter_out                   false
% 2.36/1.02  --pred_elim                             true
% 2.36/1.02  --res_sim_input                         true
% 2.36/1.02  --eq_ax_congr_red                       true
% 2.36/1.02  --pure_diseq_elim                       true
% 2.36/1.02  --brand_transform                       false
% 2.36/1.02  --non_eq_to_eq                          false
% 2.36/1.02  --prep_def_merge                        true
% 2.36/1.02  --prep_def_merge_prop_impl              false
% 2.36/1.02  --prep_def_merge_mbd                    true
% 2.36/1.02  --prep_def_merge_tr_red                 false
% 2.36/1.02  --prep_def_merge_tr_cl                  false
% 2.36/1.02  --smt_preprocessing                     true
% 2.36/1.02  --smt_ac_axioms                         fast
% 2.36/1.02  --preprocessed_out                      false
% 2.36/1.02  --preprocessed_stats                    false
% 2.36/1.02  
% 2.36/1.02  ------ Abstraction refinement Options
% 2.36/1.02  
% 2.36/1.02  --abstr_ref                             []
% 2.36/1.02  --abstr_ref_prep                        false
% 2.36/1.02  --abstr_ref_until_sat                   false
% 2.36/1.02  --abstr_ref_sig_restrict                funpre
% 2.36/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.02  --abstr_ref_under                       []
% 2.36/1.02  
% 2.36/1.02  ------ SAT Options
% 2.36/1.02  
% 2.36/1.02  --sat_mode                              false
% 2.36/1.02  --sat_fm_restart_options                ""
% 2.36/1.02  --sat_gr_def                            false
% 2.36/1.02  --sat_epr_types                         true
% 2.36/1.02  --sat_non_cyclic_types                  false
% 2.36/1.02  --sat_finite_models                     false
% 2.36/1.02  --sat_fm_lemmas                         false
% 2.36/1.02  --sat_fm_prep                           false
% 2.36/1.02  --sat_fm_uc_incr                        true
% 2.36/1.02  --sat_out_model                         small
% 2.36/1.02  --sat_out_clauses                       false
% 2.36/1.02  
% 2.36/1.02  ------ QBF Options
% 2.36/1.02  
% 2.36/1.02  --qbf_mode                              false
% 2.36/1.02  --qbf_elim_univ                         false
% 2.36/1.02  --qbf_dom_inst                          none
% 2.36/1.02  --qbf_dom_pre_inst                      false
% 2.36/1.02  --qbf_sk_in                             false
% 2.36/1.02  --qbf_pred_elim                         true
% 2.36/1.02  --qbf_split                             512
% 2.36/1.02  
% 2.36/1.02  ------ BMC1 Options
% 2.36/1.02  
% 2.36/1.02  --bmc1_incremental                      false
% 2.36/1.02  --bmc1_axioms                           reachable_all
% 2.36/1.02  --bmc1_min_bound                        0
% 2.36/1.02  --bmc1_max_bound                        -1
% 2.36/1.02  --bmc1_max_bound_default                -1
% 2.36/1.02  --bmc1_symbol_reachability              true
% 2.36/1.02  --bmc1_property_lemmas                  false
% 2.36/1.02  --bmc1_k_induction                      false
% 2.36/1.02  --bmc1_non_equiv_states                 false
% 2.36/1.02  --bmc1_deadlock                         false
% 2.36/1.02  --bmc1_ucm                              false
% 2.36/1.02  --bmc1_add_unsat_core                   none
% 2.36/1.02  --bmc1_unsat_core_children              false
% 2.36/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.02  --bmc1_out_stat                         full
% 2.36/1.02  --bmc1_ground_init                      false
% 2.36/1.02  --bmc1_pre_inst_next_state              false
% 2.36/1.02  --bmc1_pre_inst_state                   false
% 2.36/1.02  --bmc1_pre_inst_reach_state             false
% 2.36/1.02  --bmc1_out_unsat_core                   false
% 2.36/1.02  --bmc1_aig_witness_out                  false
% 2.36/1.02  --bmc1_verbose                          false
% 2.36/1.02  --bmc1_dump_clauses_tptp                false
% 2.36/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.02  --bmc1_dump_file                        -
% 2.36/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.02  --bmc1_ucm_extend_mode                  1
% 2.36/1.02  --bmc1_ucm_init_mode                    2
% 2.36/1.02  --bmc1_ucm_cone_mode                    none
% 2.36/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.02  --bmc1_ucm_relax_model                  4
% 2.36/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.02  --bmc1_ucm_layered_model                none
% 2.36/1.02  --bmc1_ucm_max_lemma_size               10
% 2.36/1.02  
% 2.36/1.02  ------ AIG Options
% 2.36/1.02  
% 2.36/1.02  --aig_mode                              false
% 2.36/1.02  
% 2.36/1.02  ------ Instantiation Options
% 2.36/1.02  
% 2.36/1.02  --instantiation_flag                    true
% 2.36/1.02  --inst_sos_flag                         false
% 2.36/1.02  --inst_sos_phase                        true
% 2.36/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.02  --inst_lit_sel_side                     num_symb
% 2.36/1.02  --inst_solver_per_active                1400
% 2.36/1.02  --inst_solver_calls_frac                1.
% 2.36/1.02  --inst_passive_queue_type               priority_queues
% 2.36/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.02  --inst_passive_queues_freq              [25;2]
% 2.36/1.02  --inst_dismatching                      true
% 2.36/1.02  --inst_eager_unprocessed_to_passive     true
% 2.36/1.02  --inst_prop_sim_given                   true
% 2.36/1.02  --inst_prop_sim_new                     false
% 2.36/1.02  --inst_subs_new                         false
% 2.36/1.02  --inst_eq_res_simp                      false
% 2.36/1.02  --inst_subs_given                       false
% 2.36/1.02  --inst_orphan_elimination               true
% 2.36/1.02  --inst_learning_loop_flag               true
% 2.36/1.02  --inst_learning_start                   3000
% 2.36/1.02  --inst_learning_factor                  2
% 2.36/1.02  --inst_start_prop_sim_after_learn       3
% 2.36/1.02  --inst_sel_renew                        solver
% 2.36/1.02  --inst_lit_activity_flag                true
% 2.36/1.02  --inst_restr_to_given                   false
% 2.36/1.02  --inst_activity_threshold               500
% 2.36/1.02  --inst_out_proof                        true
% 2.36/1.02  
% 2.36/1.02  ------ Resolution Options
% 2.36/1.02  
% 2.36/1.02  --resolution_flag                       true
% 2.36/1.02  --res_lit_sel                           adaptive
% 2.36/1.02  --res_lit_sel_side                      none
% 2.36/1.02  --res_ordering                          kbo
% 2.36/1.02  --res_to_prop_solver                    active
% 2.36/1.02  --res_prop_simpl_new                    false
% 2.36/1.02  --res_prop_simpl_given                  true
% 2.36/1.02  --res_passive_queue_type                priority_queues
% 2.36/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.02  --res_passive_queues_freq               [15;5]
% 2.36/1.02  --res_forward_subs                      full
% 2.36/1.02  --res_backward_subs                     full
% 2.36/1.02  --res_forward_subs_resolution           true
% 2.36/1.02  --res_backward_subs_resolution          true
% 2.36/1.02  --res_orphan_elimination                true
% 2.36/1.02  --res_time_limit                        2.
% 2.36/1.02  --res_out_proof                         true
% 2.36/1.02  
% 2.36/1.02  ------ Superposition Options
% 2.36/1.02  
% 2.36/1.02  --superposition_flag                    true
% 2.36/1.02  --sup_passive_queue_type                priority_queues
% 2.36/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.02  --demod_completeness_check              fast
% 2.36/1.02  --demod_use_ground                      true
% 2.36/1.02  --sup_to_prop_solver                    passive
% 2.36/1.02  --sup_prop_simpl_new                    true
% 2.36/1.02  --sup_prop_simpl_given                  true
% 2.36/1.02  --sup_fun_splitting                     false
% 2.36/1.02  --sup_smt_interval                      50000
% 2.36/1.02  
% 2.36/1.02  ------ Superposition Simplification Setup
% 2.36/1.02  
% 2.36/1.02  --sup_indices_passive                   []
% 2.36/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_full_bw                           [BwDemod]
% 2.36/1.02  --sup_immed_triv                        [TrivRules]
% 2.36/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_immed_bw_main                     []
% 2.36/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.02  
% 2.36/1.02  ------ Combination Options
% 2.36/1.02  
% 2.36/1.02  --comb_res_mult                         3
% 2.36/1.02  --comb_sup_mult                         2
% 2.36/1.02  --comb_inst_mult                        10
% 2.36/1.02  
% 2.36/1.02  ------ Debug Options
% 2.36/1.02  
% 2.36/1.02  --dbg_backtrace                         false
% 2.36/1.02  --dbg_dump_prop_clauses                 false
% 2.36/1.02  --dbg_dump_prop_clauses_file            -
% 2.36/1.02  --dbg_out_stat                          false
% 2.36/1.02  ------ Parsing...
% 2.36/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/1.02  
% 2.36/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.36/1.02  
% 2.36/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/1.02  
% 2.36/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/1.02  ------ Proving...
% 2.36/1.02  ------ Problem Properties 
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  clauses                                 18
% 2.36/1.02  conjectures                             2
% 2.36/1.02  EPR                                     9
% 2.36/1.02  Horn                                    16
% 2.36/1.02  unary                                   4
% 2.36/1.02  binary                                  6
% 2.36/1.02  lits                                    45
% 2.36/1.02  lits eq                                 6
% 2.36/1.02  fd_pure                                 0
% 2.36/1.02  fd_pseudo                               0
% 2.36/1.02  fd_cond                                 1
% 2.36/1.02  fd_pseudo_cond                          3
% 2.36/1.02  AC symbols                              0
% 2.36/1.02  
% 2.36/1.02  ------ Schedule dynamic 5 is on 
% 2.36/1.02  
% 2.36/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  ------ 
% 2.36/1.02  Current options:
% 2.36/1.02  ------ 
% 2.36/1.02  
% 2.36/1.02  ------ Input Options
% 2.36/1.02  
% 2.36/1.02  --out_options                           all
% 2.36/1.02  --tptp_safe_out                         true
% 2.36/1.02  --problem_path                          ""
% 2.36/1.02  --include_path                          ""
% 2.36/1.02  --clausifier                            res/vclausify_rel
% 2.36/1.02  --clausifier_options                    --mode clausify
% 2.36/1.02  --stdin                                 false
% 2.36/1.02  --stats_out                             all
% 2.36/1.02  
% 2.36/1.02  ------ General Options
% 2.36/1.02  
% 2.36/1.02  --fof                                   false
% 2.36/1.02  --time_out_real                         305.
% 2.36/1.02  --time_out_virtual                      -1.
% 2.36/1.02  --symbol_type_check                     false
% 2.36/1.02  --clausify_out                          false
% 2.36/1.02  --sig_cnt_out                           false
% 2.36/1.02  --trig_cnt_out                          false
% 2.36/1.02  --trig_cnt_out_tolerance                1.
% 2.36/1.02  --trig_cnt_out_sk_spl                   false
% 2.36/1.02  --abstr_cl_out                          false
% 2.36/1.02  
% 2.36/1.02  ------ Global Options
% 2.36/1.02  
% 2.36/1.02  --schedule                              default
% 2.36/1.02  --add_important_lit                     false
% 2.36/1.02  --prop_solver_per_cl                    1000
% 2.36/1.02  --min_unsat_core                        false
% 2.36/1.02  --soft_assumptions                      false
% 2.36/1.02  --soft_lemma_size                       3
% 2.36/1.02  --prop_impl_unit_size                   0
% 2.36/1.02  --prop_impl_unit                        []
% 2.36/1.02  --share_sel_clauses                     true
% 2.36/1.02  --reset_solvers                         false
% 2.36/1.02  --bc_imp_inh                            [conj_cone]
% 2.36/1.02  --conj_cone_tolerance                   3.
% 2.36/1.02  --extra_neg_conj                        none
% 2.36/1.02  --large_theory_mode                     true
% 2.36/1.02  --prolific_symb_bound                   200
% 2.36/1.02  --lt_threshold                          2000
% 2.36/1.02  --clause_weak_htbl                      true
% 2.36/1.02  --gc_record_bc_elim                     false
% 2.36/1.02  
% 2.36/1.02  ------ Preprocessing Options
% 2.36/1.02  
% 2.36/1.02  --preprocessing_flag                    true
% 2.36/1.02  --time_out_prep_mult                    0.1
% 2.36/1.02  --splitting_mode                        input
% 2.36/1.02  --splitting_grd                         true
% 2.36/1.02  --splitting_cvd                         false
% 2.36/1.02  --splitting_cvd_svl                     false
% 2.36/1.02  --splitting_nvd                         32
% 2.36/1.02  --sub_typing                            true
% 2.36/1.02  --prep_gs_sim                           true
% 2.36/1.02  --prep_unflatten                        true
% 2.36/1.02  --prep_res_sim                          true
% 2.36/1.02  --prep_upred                            true
% 2.36/1.02  --prep_sem_filter                       exhaustive
% 2.36/1.02  --prep_sem_filter_out                   false
% 2.36/1.02  --pred_elim                             true
% 2.36/1.02  --res_sim_input                         true
% 2.36/1.02  --eq_ax_congr_red                       true
% 2.36/1.02  --pure_diseq_elim                       true
% 2.36/1.02  --brand_transform                       false
% 2.36/1.02  --non_eq_to_eq                          false
% 2.36/1.02  --prep_def_merge                        true
% 2.36/1.02  --prep_def_merge_prop_impl              false
% 2.36/1.02  --prep_def_merge_mbd                    true
% 2.36/1.02  --prep_def_merge_tr_red                 false
% 2.36/1.02  --prep_def_merge_tr_cl                  false
% 2.36/1.02  --smt_preprocessing                     true
% 2.36/1.02  --smt_ac_axioms                         fast
% 2.36/1.02  --preprocessed_out                      false
% 2.36/1.02  --preprocessed_stats                    false
% 2.36/1.02  
% 2.36/1.02  ------ Abstraction refinement Options
% 2.36/1.02  
% 2.36/1.02  --abstr_ref                             []
% 2.36/1.02  --abstr_ref_prep                        false
% 2.36/1.02  --abstr_ref_until_sat                   false
% 2.36/1.02  --abstr_ref_sig_restrict                funpre
% 2.36/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.02  --abstr_ref_under                       []
% 2.36/1.02  
% 2.36/1.02  ------ SAT Options
% 2.36/1.02  
% 2.36/1.02  --sat_mode                              false
% 2.36/1.02  --sat_fm_restart_options                ""
% 2.36/1.02  --sat_gr_def                            false
% 2.36/1.02  --sat_epr_types                         true
% 2.36/1.02  --sat_non_cyclic_types                  false
% 2.36/1.02  --sat_finite_models                     false
% 2.36/1.02  --sat_fm_lemmas                         false
% 2.36/1.02  --sat_fm_prep                           false
% 2.36/1.02  --sat_fm_uc_incr                        true
% 2.36/1.02  --sat_out_model                         small
% 2.36/1.02  --sat_out_clauses                       false
% 2.36/1.02  
% 2.36/1.02  ------ QBF Options
% 2.36/1.02  
% 2.36/1.02  --qbf_mode                              false
% 2.36/1.02  --qbf_elim_univ                         false
% 2.36/1.02  --qbf_dom_inst                          none
% 2.36/1.02  --qbf_dom_pre_inst                      false
% 2.36/1.02  --qbf_sk_in                             false
% 2.36/1.02  --qbf_pred_elim                         true
% 2.36/1.02  --qbf_split                             512
% 2.36/1.02  
% 2.36/1.02  ------ BMC1 Options
% 2.36/1.02  
% 2.36/1.02  --bmc1_incremental                      false
% 2.36/1.02  --bmc1_axioms                           reachable_all
% 2.36/1.02  --bmc1_min_bound                        0
% 2.36/1.02  --bmc1_max_bound                        -1
% 2.36/1.02  --bmc1_max_bound_default                -1
% 2.36/1.02  --bmc1_symbol_reachability              true
% 2.36/1.02  --bmc1_property_lemmas                  false
% 2.36/1.02  --bmc1_k_induction                      false
% 2.36/1.02  --bmc1_non_equiv_states                 false
% 2.36/1.02  --bmc1_deadlock                         false
% 2.36/1.02  --bmc1_ucm                              false
% 2.36/1.02  --bmc1_add_unsat_core                   none
% 2.36/1.02  --bmc1_unsat_core_children              false
% 2.36/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.02  --bmc1_out_stat                         full
% 2.36/1.02  --bmc1_ground_init                      false
% 2.36/1.02  --bmc1_pre_inst_next_state              false
% 2.36/1.02  --bmc1_pre_inst_state                   false
% 2.36/1.02  --bmc1_pre_inst_reach_state             false
% 2.36/1.02  --bmc1_out_unsat_core                   false
% 2.36/1.02  --bmc1_aig_witness_out                  false
% 2.36/1.02  --bmc1_verbose                          false
% 2.36/1.02  --bmc1_dump_clauses_tptp                false
% 2.36/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.02  --bmc1_dump_file                        -
% 2.36/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.02  --bmc1_ucm_extend_mode                  1
% 2.36/1.02  --bmc1_ucm_init_mode                    2
% 2.36/1.02  --bmc1_ucm_cone_mode                    none
% 2.36/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.02  --bmc1_ucm_relax_model                  4
% 2.36/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.02  --bmc1_ucm_layered_model                none
% 2.36/1.02  --bmc1_ucm_max_lemma_size               10
% 2.36/1.02  
% 2.36/1.02  ------ AIG Options
% 2.36/1.02  
% 2.36/1.02  --aig_mode                              false
% 2.36/1.02  
% 2.36/1.02  ------ Instantiation Options
% 2.36/1.02  
% 2.36/1.02  --instantiation_flag                    true
% 2.36/1.02  --inst_sos_flag                         false
% 2.36/1.02  --inst_sos_phase                        true
% 2.36/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.02  --inst_lit_sel_side                     none
% 2.36/1.02  --inst_solver_per_active                1400
% 2.36/1.02  --inst_solver_calls_frac                1.
% 2.36/1.02  --inst_passive_queue_type               priority_queues
% 2.36/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.02  --inst_passive_queues_freq              [25;2]
% 2.36/1.02  --inst_dismatching                      true
% 2.36/1.02  --inst_eager_unprocessed_to_passive     true
% 2.36/1.02  --inst_prop_sim_given                   true
% 2.36/1.02  --inst_prop_sim_new                     false
% 2.36/1.02  --inst_subs_new                         false
% 2.36/1.02  --inst_eq_res_simp                      false
% 2.36/1.02  --inst_subs_given                       false
% 2.36/1.02  --inst_orphan_elimination               true
% 2.36/1.02  --inst_learning_loop_flag               true
% 2.36/1.02  --inst_learning_start                   3000
% 2.36/1.02  --inst_learning_factor                  2
% 2.36/1.02  --inst_start_prop_sim_after_learn       3
% 2.36/1.02  --inst_sel_renew                        solver
% 2.36/1.02  --inst_lit_activity_flag                true
% 2.36/1.02  --inst_restr_to_given                   false
% 2.36/1.02  --inst_activity_threshold               500
% 2.36/1.02  --inst_out_proof                        true
% 2.36/1.02  
% 2.36/1.02  ------ Resolution Options
% 2.36/1.02  
% 2.36/1.02  --resolution_flag                       false
% 2.36/1.02  --res_lit_sel                           adaptive
% 2.36/1.02  --res_lit_sel_side                      none
% 2.36/1.02  --res_ordering                          kbo
% 2.36/1.02  --res_to_prop_solver                    active
% 2.36/1.02  --res_prop_simpl_new                    false
% 2.36/1.02  --res_prop_simpl_given                  true
% 2.36/1.02  --res_passive_queue_type                priority_queues
% 2.36/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.02  --res_passive_queues_freq               [15;5]
% 2.36/1.02  --res_forward_subs                      full
% 2.36/1.02  --res_backward_subs                     full
% 2.36/1.02  --res_forward_subs_resolution           true
% 2.36/1.02  --res_backward_subs_resolution          true
% 2.36/1.02  --res_orphan_elimination                true
% 2.36/1.02  --res_time_limit                        2.
% 2.36/1.02  --res_out_proof                         true
% 2.36/1.02  
% 2.36/1.02  ------ Superposition Options
% 2.36/1.02  
% 2.36/1.02  --superposition_flag                    true
% 2.36/1.02  --sup_passive_queue_type                priority_queues
% 2.36/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.02  --demod_completeness_check              fast
% 2.36/1.02  --demod_use_ground                      true
% 2.36/1.02  --sup_to_prop_solver                    passive
% 2.36/1.02  --sup_prop_simpl_new                    true
% 2.36/1.02  --sup_prop_simpl_given                  true
% 2.36/1.02  --sup_fun_splitting                     false
% 2.36/1.02  --sup_smt_interval                      50000
% 2.36/1.02  
% 2.36/1.02  ------ Superposition Simplification Setup
% 2.36/1.02  
% 2.36/1.02  --sup_indices_passive                   []
% 2.36/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_full_bw                           [BwDemod]
% 2.36/1.02  --sup_immed_triv                        [TrivRules]
% 2.36/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_immed_bw_main                     []
% 2.36/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.02  
% 2.36/1.02  ------ Combination Options
% 2.36/1.02  
% 2.36/1.02  --comb_res_mult                         3
% 2.36/1.02  --comb_sup_mult                         2
% 2.36/1.02  --comb_inst_mult                        10
% 2.36/1.02  
% 2.36/1.02  ------ Debug Options
% 2.36/1.02  
% 2.36/1.02  --dbg_backtrace                         false
% 2.36/1.02  --dbg_dump_prop_clauses                 false
% 2.36/1.02  --dbg_dump_prop_clauses_file            -
% 2.36/1.02  --dbg_out_stat                          false
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  ------ Proving...
% 2.36/1.02  
% 2.36/1.02  
% 2.36/1.02  % SZS status Theorem for theBenchmark.p
% 2.36/1.02  
% 2.36/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/1.02  
% 2.36/1.02  fof(f13,conjecture,(
% 2.36/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f14,negated_conjecture,(
% 2.36/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.36/1.02    inference(negated_conjecture,[],[f13])).
% 2.36/1.02  
% 2.36/1.02  fof(f31,plain,(
% 2.36/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f14])).
% 2.36/1.02  
% 2.36/1.02  fof(f32,plain,(
% 2.36/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f31])).
% 2.36/1.02  
% 2.36/1.02  fof(f39,plain,(
% 2.36/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.36/1.02    inference(nnf_transformation,[],[f32])).
% 2.36/1.02  
% 2.36/1.02  fof(f40,plain,(
% 2.36/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f39])).
% 2.36/1.02  
% 2.36/1.02  fof(f44,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.36/1.02    introduced(choice_axiom,[])).
% 2.36/1.02  
% 2.36/1.02  fof(f43,plain,(
% 2.36/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.36/1.02    introduced(choice_axiom,[])).
% 2.36/1.02  
% 2.36/1.02  fof(f42,plain,(
% 2.36/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.36/1.02    introduced(choice_axiom,[])).
% 2.36/1.02  
% 2.36/1.02  fof(f41,plain,(
% 2.36/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.36/1.02    introduced(choice_axiom,[])).
% 2.36/1.02  
% 2.36/1.02  fof(f45,plain,(
% 2.36/1.02    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.36/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43,f42,f41])).
% 2.36/1.02  
% 2.36/1.02  fof(f70,plain,(
% 2.36/1.02    m2_orders_2(sK2,sK0,sK1)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f8,axiom,(
% 2.36/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f15,plain,(
% 2.36/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.36/1.02    inference(pure_predicate_removal,[],[f8])).
% 2.36/1.02  
% 2.36/1.02  fof(f21,plain,(
% 2.36/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f15])).
% 2.36/1.02  
% 2.36/1.02  fof(f22,plain,(
% 2.36/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f21])).
% 2.36/1.02  
% 2.36/1.02  fof(f58,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f22])).
% 2.36/1.02  
% 2.36/1.02  fof(f69,plain,(
% 2.36/1.02    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f68,plain,(
% 2.36/1.02    l1_orders_2(sK0)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f64,plain,(
% 2.36/1.02    ~v2_struct_0(sK0)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f65,plain,(
% 2.36/1.02    v3_orders_2(sK0)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f66,plain,(
% 2.36/1.02    v4_orders_2(sK0)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f67,plain,(
% 2.36/1.02    v5_orders_2(sK0)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f10,axiom,(
% 2.36/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f25,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f10])).
% 2.36/1.02  
% 2.36/1.02  fof(f26,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f25])).
% 2.36/1.02  
% 2.36/1.02  fof(f60,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f26])).
% 2.36/1.02  
% 2.36/1.02  fof(f7,axiom,(
% 2.36/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f19,plain,(
% 2.36/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f7])).
% 2.36/1.02  
% 2.36/1.02  fof(f20,plain,(
% 2.36/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f19])).
% 2.36/1.02  
% 2.36/1.02  fof(f57,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f20])).
% 2.36/1.02  
% 2.36/1.02  fof(f4,axiom,(
% 2.36/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f37,plain,(
% 2.36/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.36/1.02    inference(nnf_transformation,[],[f4])).
% 2.36/1.02  
% 2.36/1.02  fof(f53,plain,(
% 2.36/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.36/1.02    inference(cnf_transformation,[],[f37])).
% 2.36/1.02  
% 2.36/1.02  fof(f1,axiom,(
% 2.36/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f33,plain,(
% 2.36/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.36/1.02    inference(nnf_transformation,[],[f1])).
% 2.36/1.02  
% 2.36/1.02  fof(f34,plain,(
% 2.36/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.36/1.02    inference(flattening,[],[f33])).
% 2.36/1.02  
% 2.36/1.02  fof(f47,plain,(
% 2.36/1.02    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f34])).
% 2.36/1.02  
% 2.36/1.02  fof(f74,plain,(
% 2.36/1.02    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.36/1.02    inference(equality_resolution,[],[f47])).
% 2.36/1.02  
% 2.36/1.02  fof(f72,plain,(
% 2.36/1.02    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f46,plain,(
% 2.36/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f34])).
% 2.36/1.02  
% 2.36/1.02  fof(f2,axiom,(
% 2.36/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f35,plain,(
% 2.36/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.36/1.02    inference(nnf_transformation,[],[f2])).
% 2.36/1.02  
% 2.36/1.02  fof(f36,plain,(
% 2.36/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.36/1.02    inference(flattening,[],[f35])).
% 2.36/1.02  
% 2.36/1.02  fof(f51,plain,(
% 2.36/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f36])).
% 2.36/1.02  
% 2.36/1.02  fof(f71,plain,(
% 2.36/1.02    m2_orders_2(sK3,sK0,sK1)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f12,axiom,(
% 2.36/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f29,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f12])).
% 2.36/1.02  
% 2.36/1.02  fof(f30,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f29])).
% 2.36/1.02  
% 2.36/1.02  fof(f38,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(nnf_transformation,[],[f30])).
% 2.36/1.02  
% 2.36/1.02  fof(f63,plain,(
% 2.36/1.02    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f38])).
% 2.36/1.02  
% 2.36/1.02  fof(f9,axiom,(
% 2.36/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f23,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f9])).
% 2.36/1.02  
% 2.36/1.02  fof(f24,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f23])).
% 2.36/1.02  
% 2.36/1.02  fof(f59,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f24])).
% 2.36/1.02  
% 2.36/1.02  fof(f62,plain,(
% 2.36/1.02    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f38])).
% 2.36/1.02  
% 2.36/1.02  fof(f48,plain,(
% 2.36/1.02    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f34])).
% 2.36/1.02  
% 2.36/1.02  fof(f73,plain,(
% 2.36/1.02    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.36/1.02    inference(cnf_transformation,[],[f45])).
% 2.36/1.02  
% 2.36/1.02  fof(f54,plain,(
% 2.36/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f37])).
% 2.36/1.02  
% 2.36/1.02  fof(f3,axiom,(
% 2.36/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f52,plain,(
% 2.36/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.36/1.02    inference(cnf_transformation,[],[f3])).
% 2.36/1.02  
% 2.36/1.02  fof(f6,axiom,(
% 2.36/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f18,plain,(
% 2.36/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.36/1.02    inference(ennf_transformation,[],[f6])).
% 2.36/1.02  
% 2.36/1.02  fof(f56,plain,(
% 2.36/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f18])).
% 2.36/1.02  
% 2.36/1.02  fof(f11,axiom,(
% 2.36/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 2.36/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.02  
% 2.36/1.02  fof(f27,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/1.02    inference(ennf_transformation,[],[f11])).
% 2.36/1.02  
% 2.36/1.02  fof(f28,plain,(
% 2.36/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.36/1.02    inference(flattening,[],[f27])).
% 2.36/1.02  
% 2.36/1.02  fof(f61,plain,(
% 2.36/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/1.02    inference(cnf_transformation,[],[f28])).
% 2.36/1.02  
% 2.36/1.02  cnf(c_21,negated_conjecture,
% 2.36/1.02      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.36/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_1578,plain,
% 2.36/1.02      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.36/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_12,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.02      | v2_struct_0(X1)
% 2.36/1.02      | ~ v3_orders_2(X1)
% 2.36/1.02      | ~ v4_orders_2(X1)
% 2.36/1.02      | ~ v5_orders_2(X1)
% 2.36/1.02      | ~ l1_orders_2(X1) ),
% 2.36/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_22,negated_conjecture,
% 2.36/1.02      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.36/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_597,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.02      | v2_struct_0(X1)
% 2.36/1.02      | ~ v3_orders_2(X1)
% 2.36/1.02      | ~ v4_orders_2(X1)
% 2.36/1.02      | ~ v5_orders_2(X1)
% 2.36/1.02      | ~ l1_orders_2(X1)
% 2.36/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.02      | sK1 != X2 ),
% 2.36/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_598,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.02      | v2_struct_0(X1)
% 2.36/1.02      | ~ v3_orders_2(X1)
% 2.36/1.02      | ~ v4_orders_2(X1)
% 2.36/1.02      | ~ v5_orders_2(X1)
% 2.36/1.02      | ~ l1_orders_2(X1)
% 2.36/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.02      inference(unflattening,[status(thm)],[c_597]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_23,negated_conjecture,
% 2.36/1.02      ( l1_orders_2(sK0) ),
% 2.36/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_727,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.02      | v2_struct_0(X1)
% 2.36/1.02      | ~ v3_orders_2(X1)
% 2.36/1.02      | ~ v4_orders_2(X1)
% 2.36/1.02      | ~ v5_orders_2(X1)
% 2.36/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.02      | sK0 != X1 ),
% 2.36/1.02      inference(resolution_lifted,[status(thm)],[c_598,c_23]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_728,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.02      | v2_struct_0(sK0)
% 2.36/1.02      | ~ v3_orders_2(sK0)
% 2.36/1.02      | ~ v4_orders_2(sK0)
% 2.36/1.02      | ~ v5_orders_2(sK0)
% 2.36/1.02      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.02      inference(unflattening,[status(thm)],[c_727]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_27,negated_conjecture,
% 2.36/1.02      ( ~ v2_struct_0(sK0) ),
% 2.36/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_26,negated_conjecture,
% 2.36/1.02      ( v3_orders_2(sK0) ),
% 2.36/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_25,negated_conjecture,
% 2.36/1.02      ( v4_orders_2(sK0) ),
% 2.36/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_24,negated_conjecture,
% 2.36/1.02      ( v5_orders_2(sK0) ),
% 2.36/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_732,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.02      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.02      inference(global_propositional_subsumption,
% 2.36/1.02                [status(thm)],
% 2.36/1.02                [c_728,c_27,c_26,c_25,c_24]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_987,plain,
% 2.36/1.02      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.36/1.02      inference(equality_resolution_simp,[status(thm)],[c_732]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_1568,plain,
% 2.36/1.02      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.36/1.02      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 2.36/1.02  
% 2.36/1.02  cnf(c_14,plain,
% 2.36/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | k1_xboole_0 = X2 ),
% 2.36/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_11,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_154,plain,
% 2.36/1.03      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | k1_xboole_0 = X2 ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_14,c_11]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_155,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | k1_xboole_0 = X2 ),
% 2.36/1.03      inference(renaming,[status(thm)],[c_154]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_829,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | sK0 != X1
% 2.36/1.03      | k1_xboole_0 = X2 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_155,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_830,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0)
% 2.36/1.03      | k1_xboole_0 = X0 ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_829]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_834,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | k1_xboole_0 = X0 ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_830,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_835,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | k1_xboole_0 = X1 ),
% 2.36/1.03      inference(renaming,[status(thm)],[c_834]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1574,plain,
% 2.36/1.03      ( k1_xboole_0 = X0
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1833,plain,
% 2.36/1.03      ( k1_xboole_0 = X0
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1568,c_1574]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4665,plain,
% 2.36/1.03      ( sK2 = k1_xboole_0
% 2.36/1.03      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.36/1.03      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1578,c_1833]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_34,plain,
% 2.36/1.03      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1724,plain,
% 2.36/1.03      ( ~ m2_orders_2(sK2,sK0,sK1)
% 2.36/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_987]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1725,plain,
% 2.36/1.03      ( m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_8,plain,
% 2.36/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1919,plain,
% 2.36/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2258,plain,
% 2.36/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_1919]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2259,plain,
% 2.36/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.36/1.03      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1,plain,
% 2.36/1.03      ( ~ r2_xboole_0(X0,X0) ),
% 2.36/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_19,negated_conjecture,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.36/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_211,plain,
% 2.36/1.03      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.36/1.03      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_212,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.36/1.03      inference(renaming,[status(thm)],[c_211]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_389,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_212]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_390,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_389]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1575,plain,
% 2.36/1.03      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2,plain,
% 2.36/1.03      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_379,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3)
% 2.36/1.03      | r1_tarski(X0,X1)
% 2.36/1.03      | sK3 != X1
% 2.36/1.03      | sK2 != X0 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_212]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_380,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_379]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_381,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.36/1.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_391,plain,
% 2.36/1.03      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3,plain,
% 2.36/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.36/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2215,plain,
% 2.36/1.03      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2927,plain,
% 2.36/1.03      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_2215]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2928,plain,
% 2.36/1.03      ( sK2 = sK3
% 2.36/1.03      | r1_tarski(sK3,sK2) != iProver_top
% 2.36/1.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_2927]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_20,negated_conjecture,
% 2.36/1.03      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1579,plain,
% 2.36/1.03      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_16,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.36/1.03      | m1_orders_2(X3,X1,X0)
% 2.36/1.03      | m1_orders_2(X0,X1,X3)
% 2.36/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X3 = X0 ),
% 2.36/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_528,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.36/1.03      | m1_orders_2(X3,X1,X0)
% 2.36/1.03      | m1_orders_2(X0,X1,X3)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X3 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK1 != X2 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_529,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.36/1.03      | m1_orders_2(X0,X1,X2)
% 2.36/1.03      | m1_orders_2(X2,X1,X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X0 = X2
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_528]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_769,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.36/1.03      | m1_orders_2(X0,X1,X2)
% 2.36/1.03      | m1_orders_2(X2,X1,X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | X2 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK0 != X1 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_529,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_770,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0)
% 2.36/1.03      | X1 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_769]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_774,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | X1 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_770,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_983,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | X1 = X0 ),
% 2.36/1.03      inference(equality_resolution_simp,[status(thm)],[c_774]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1569,plain,
% 2.36/1.03      ( X0 = X1
% 2.36/1.03      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2756,plain,
% 2.36/1.03      ( sK3 = X0
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.36/1.03      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1579,c_1569]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3200,plain,
% 2.36/1.03      ( sK3 = sK2
% 2.36/1.03      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1578,c_2756]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_35,plain,
% 2.36/1.03      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2140,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.36/1.03      | m1_orders_2(X0,sK0,sK2)
% 2.36/1.03      | m1_orders_2(sK2,sK0,X0)
% 2.36/1.03      | sK2 = X0 ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_983]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2710,plain,
% 2.36/1.03      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.36/1.03      | m1_orders_2(sK3,sK0,sK2)
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK3)
% 2.36/1.03      | sK2 = sK3 ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_2140]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2711,plain,
% 2.36/1.03      ( sK2 = sK3
% 2.36/1.03      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.36/1.03      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_2710]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3209,plain,
% 2.36/1.03      ( m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_3200,c_34,c_35,c_391,c_2711]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_13,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | r1_tarski(X0,X2)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_853,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | r1_tarski(X0,X2)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | sK0 != X1 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_854,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | r1_tarski(X0,X1)
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_853]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_856,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | r1_tarski(X0,X1) ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_854,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1573,plain,
% 2.36/1.03      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.36/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1835,plain,
% 2.36/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | r1_tarski(X1,X0) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1568,c_1573]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1986,plain,
% 2.36/1.03      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.36/1.03      | r1_tarski(X0,sK2) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1578,c_1835]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3215,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.36/1.03      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_3209,c_1986]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4065,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_1575,c_381,c_391,c_2928,c_3215]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_17,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X3,X1,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,X1,X3)
% 2.36/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X3 = X0 ),
% 2.36/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_489,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X3,X1,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,X1,X3)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X3 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK1 != X2 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_490,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.36/1.03      | ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | X0 = X2
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_489]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_799,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.36/1.03      | ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_orders_2(X2,X1,X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | X2 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK0 != X1 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_490,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_800,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0)
% 2.36/1.03      | X1 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_799]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_804,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | X1 = X0
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_800,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_979,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.36/1.03      | ~ m1_orders_2(X1,sK0,X0)
% 2.36/1.03      | ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | X1 = X0 ),
% 2.36/1.03      inference(equality_resolution_simp,[status(thm)],[c_804]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1570,plain,
% 2.36/1.03      ( X0 = X1
% 2.36/1.03      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_76,plain,
% 2.36/1.03      ( X0 = X1
% 2.36/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.36/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_858,plain,
% 2.36/1.03      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.36/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_870,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | sK0 != X1 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_871,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_870]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_873,plain,
% 2.36/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_871,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1572,plain,
% 2.36/1.03      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.36/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1834,plain,
% 2.36/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1568,c_1572]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3493,plain,
% 2.36/1.03      ( X0 = X1
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_1570,c_76,c_858,c_1834,c_1835]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3494,plain,
% 2.36/1.03      ( X0 = X1
% 2.36/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.36/1.03      inference(renaming,[status(thm)],[c_3493]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_3501,plain,
% 2.36/1.03      ( sK3 = X0
% 2.36/1.03      | m1_orders_2(X0,sK0,sK3) != iProver_top
% 2.36/1.03      | m1_orders_2(sK3,sK0,X0) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1579,c_3494]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4076,plain,
% 2.36/1.03      ( sK3 = sK2 | m1_orders_2(sK3,sK0,sK2) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_4065,c_3501]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_0,plain,
% 2.36/1.03      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.36/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_18,negated_conjecture,
% 2.36/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.36/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_209,plain,
% 2.36/1.03      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.36/1.03      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_210,plain,
% 2.36/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.36/1.03      inference(renaming,[status(thm)],[c_209]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_366,plain,
% 2.36/1.03      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.36/1.03      | ~ r1_tarski(X0,X1)
% 2.36/1.03      | X1 = X0
% 2.36/1.03      | sK3 != X1
% 2.36/1.03      | sK2 != X0 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_210]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_367,plain,
% 2.36/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_366]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_368,plain,
% 2.36/1.03      ( sK3 = sK2
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.36/1.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1721,plain,
% 2.36/1.03      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.36/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_987]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1722,plain,
% 2.36/1.03      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.36/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1741,plain,
% 2.36/1.03      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.36/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.36/1.03      | r1_tarski(sK2,sK3) ),
% 2.36/1.03      inference(instantiation,[status(thm)],[c_856]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1742,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.36/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.36/1.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4508,plain,
% 2.36/1.03      ( sK3 = sK2 ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_4076,c_35,c_368,c_381,c_391,c_1722,c_1742,c_2928,
% 2.36/1.03                 c_3215]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4520,plain,
% 2.36/1.03      ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 2.36/1.03      inference(demodulation,[status(thm)],[c_4508,c_3209]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_7,plain,
% 2.36/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1581,plain,
% 2.36/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.36/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2265,plain,
% 2.36/1.03      ( k1_xboole_0 = X0
% 2.36/1.03      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.36/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.36/1.03      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1581,c_1574]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4572,plain,
% 2.36/1.03      ( sK2 = k1_xboole_0
% 2.36/1.03      | m1_orders_2(sK2,sK0,sK2) != iProver_top
% 2.36/1.03      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_4520,c_2265]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4592,plain,
% 2.36/1.03      ( sK2 = k1_xboole_0
% 2.36/1.03      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 2.36/1.03      inference(forward_subsumption_resolution,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_4572,c_4520]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4735,plain,
% 2.36/1.03      ( sK2 = k1_xboole_0 ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_4665,c_34,c_1725,c_2259,c_4592]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_4752,plain,
% 2.36/1.03      ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
% 2.36/1.03      inference(demodulation,[status(thm)],[c_4735,c_1578]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_6,plain,
% 2.36/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.36/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1582,plain,
% 2.36/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1580,plain,
% 2.36/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.36/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2200,plain,
% 2.36/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_1582,c_1580]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_10,plain,
% 2.36/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.36/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_15,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.36/1.03      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1) ),
% 2.36/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_567,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.36/1.03      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK1 != X2 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_568,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | r2_hidden(k1_funct_1(sK1,u1_struct_0(X1)),X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | ~ l1_orders_2(X1)
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_567]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_748,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.36/1.03      | r2_hidden(k1_funct_1(sK1,u1_struct_0(X1)),X0)
% 2.36/1.03      | v2_struct_0(X1)
% 2.36/1.03      | ~ v3_orders_2(X1)
% 2.36/1.03      | ~ v4_orders_2(X1)
% 2.36/1.03      | ~ v5_orders_2(X1)
% 2.36/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.36/1.03      | sK0 != X1 ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_568,c_23]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_749,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
% 2.36/1.03      | v2_struct_0(sK0)
% 2.36/1.03      | ~ v3_orders_2(sK0)
% 2.36/1.03      | ~ v4_orders_2(sK0)
% 2.36/1.03      | ~ v5_orders_2(sK0)
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_748]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_753,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(global_propositional_subsumption,
% 2.36/1.03                [status(thm)],
% 2.36/1.03                [c_749,c_27,c_26,c_25,c_24]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_922,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ r1_tarski(X1,X2)
% 2.36/1.03      | X0 != X1
% 2.36/1.03      | k1_funct_1(sK1,u1_struct_0(sK0)) != X2
% 2.36/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.36/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_753]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_923,plain,
% 2.36/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.36/1.03      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
% 2.36/1.03      inference(unflattening,[status(thm)],[c_922]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_1571,plain,
% 2.36/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.36/1.03      | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
% 2.36/1.03      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(c_2913,plain,
% 2.36/1.03      ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 2.36/1.03      inference(superposition,[status(thm)],[c_2200,c_1571]) ).
% 2.36/1.03  
% 2.36/1.03  cnf(contradiction,plain,
% 2.36/1.03      ( $false ),
% 2.36/1.03      inference(minisat,[status(thm)],[c_4752,c_2913]) ).
% 2.36/1.03  
% 2.36/1.03  
% 2.36/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/1.03  
% 2.36/1.03  ------                               Statistics
% 2.36/1.03  
% 2.36/1.03  ------ General
% 2.36/1.03  
% 2.36/1.03  abstr_ref_over_cycles:                  0
% 2.36/1.03  abstr_ref_under_cycles:                 0
% 2.36/1.03  gc_basic_clause_elim:                   0
% 2.36/1.03  forced_gc_time:                         0
% 2.36/1.03  parsing_time:                           0.013
% 2.36/1.03  unif_index_cands_time:                  0.
% 2.36/1.03  unif_index_add_time:                    0.
% 2.36/1.03  orderings_time:                         0.
% 2.36/1.03  out_proof_time:                         0.011
% 2.36/1.03  total_time:                             0.202
% 2.36/1.03  num_of_symbols:                         52
% 2.36/1.03  num_of_terms:                           2228
% 2.36/1.03  
% 2.36/1.03  ------ Preprocessing
% 2.36/1.03  
% 2.36/1.03  num_of_splits:                          0
% 2.36/1.03  num_of_split_atoms:                     0
% 2.36/1.03  num_of_reused_defs:                     0
% 2.36/1.03  num_eq_ax_congr_red:                    4
% 2.36/1.03  num_of_sem_filtered_clauses:            1
% 2.36/1.03  num_of_subtypes:                        0
% 2.36/1.03  monotx_restored_types:                  0
% 2.36/1.03  sat_num_of_epr_types:                   0
% 2.36/1.03  sat_num_of_non_cyclic_types:            0
% 2.36/1.03  sat_guarded_non_collapsed_types:        0
% 2.36/1.03  num_pure_diseq_elim:                    0
% 2.36/1.03  simp_replaced_by:                       0
% 2.36/1.03  res_preprocessed:                       100
% 2.36/1.03  prep_upred:                             0
% 2.36/1.03  prep_unflattend:                        30
% 2.36/1.03  smt_new_axioms:                         0
% 2.36/1.03  pred_elim_cands:                        4
% 2.36/1.03  pred_elim:                              8
% 2.36/1.03  pred_elim_cl:                           9
% 2.36/1.03  pred_elim_cycles:                       12
% 2.36/1.03  merged_defs:                            10
% 2.36/1.03  merged_defs_ncl:                        0
% 2.36/1.03  bin_hyper_res:                          11
% 2.36/1.03  prep_cycles:                            4
% 2.36/1.03  pred_elim_time:                         0.021
% 2.36/1.03  splitting_time:                         0.
% 2.36/1.03  sem_filter_time:                        0.
% 2.36/1.03  monotx_time:                            0.001
% 2.36/1.03  subtype_inf_time:                       0.
% 2.36/1.03  
% 2.36/1.03  ------ Problem properties
% 2.36/1.03  
% 2.36/1.03  clauses:                                18
% 2.36/1.03  conjectures:                            2
% 2.36/1.03  epr:                                    9
% 2.36/1.03  horn:                                   16
% 2.36/1.03  ground:                                 5
% 2.36/1.03  unary:                                  4
% 2.36/1.03  binary:                                 6
% 2.36/1.03  lits:                                   45
% 2.36/1.03  lits_eq:                                6
% 2.36/1.03  fd_pure:                                0
% 2.36/1.03  fd_pseudo:                              0
% 2.36/1.03  fd_cond:                                1
% 2.36/1.03  fd_pseudo_cond:                         3
% 2.36/1.03  ac_symbols:                             0
% 2.36/1.03  
% 2.36/1.03  ------ Propositional Solver
% 2.36/1.03  
% 2.36/1.03  prop_solver_calls:                      29
% 2.36/1.03  prop_fast_solver_calls:                 912
% 2.36/1.03  smt_solver_calls:                       0
% 2.36/1.03  smt_fast_solver_calls:                  0
% 2.36/1.03  prop_num_of_clauses:                    1532
% 2.36/1.03  prop_preprocess_simplified:             4407
% 2.36/1.03  prop_fo_subsumed:                       35
% 2.36/1.03  prop_solver_time:                       0.
% 2.36/1.03  smt_solver_time:                        0.
% 2.36/1.03  smt_fast_solver_time:                   0.
% 2.36/1.03  prop_fast_solver_time:                  0.
% 2.36/1.03  prop_unsat_core_time:                   0.
% 2.36/1.03  
% 2.36/1.03  ------ QBF
% 2.36/1.03  
% 2.36/1.03  qbf_q_res:                              0
% 2.36/1.03  qbf_num_tautologies:                    0
% 2.36/1.03  qbf_prep_cycles:                        0
% 2.36/1.03  
% 2.36/1.03  ------ BMC1
% 2.36/1.03  
% 2.36/1.03  bmc1_current_bound:                     -1
% 2.36/1.03  bmc1_last_solved_bound:                 -1
% 2.36/1.03  bmc1_unsat_core_size:                   -1
% 2.36/1.03  bmc1_unsat_core_parents_size:           -1
% 2.36/1.03  bmc1_merge_next_fun:                    0
% 2.36/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.03  
% 2.36/1.03  ------ Instantiation
% 2.36/1.03  
% 2.36/1.03  inst_num_of_clauses:                    406
% 2.36/1.03  inst_num_in_passive:                    65
% 2.36/1.03  inst_num_in_active:                     284
% 2.36/1.03  inst_num_in_unprocessed:                59
% 2.36/1.03  inst_num_of_loops:                      300
% 2.36/1.03  inst_num_of_learning_restarts:          0
% 2.36/1.03  inst_num_moves_active_passive:          12
% 2.36/1.03  inst_lit_activity:                      0
% 2.36/1.03  inst_lit_activity_moves:                0
% 2.36/1.03  inst_num_tautologies:                   0
% 2.36/1.03  inst_num_prop_implied:                  0
% 2.36/1.03  inst_num_existing_simplified:           0
% 2.36/1.03  inst_num_eq_res_simplified:             0
% 2.36/1.03  inst_num_child_elim:                    0
% 2.36/1.03  inst_num_of_dismatching_blockings:      120
% 2.36/1.03  inst_num_of_non_proper_insts:           571
% 2.36/1.03  inst_num_of_duplicates:                 0
% 2.36/1.03  inst_inst_num_from_inst_to_res:         0
% 2.36/1.03  inst_dismatching_checking_time:         0.
% 2.36/1.03  
% 2.36/1.03  ------ Resolution
% 2.36/1.03  
% 2.36/1.03  res_num_of_clauses:                     0
% 2.36/1.03  res_num_in_passive:                     0
% 2.36/1.03  res_num_in_active:                      0
% 2.36/1.03  res_num_of_loops:                       104
% 2.36/1.03  res_forward_subset_subsumed:            75
% 2.36/1.03  res_backward_subset_subsumed:           4
% 2.36/1.03  res_forward_subsumed:                   0
% 2.36/1.03  res_backward_subsumed:                  0
% 2.36/1.03  res_forward_subsumption_resolution:     0
% 2.36/1.03  res_backward_subsumption_resolution:    0
% 2.36/1.03  res_clause_to_clause_subsumption:       275
% 2.36/1.03  res_orphan_elimination:                 0
% 2.36/1.03  res_tautology_del:                      60
% 2.36/1.03  res_num_eq_res_simplified:              3
% 2.36/1.03  res_num_sel_changes:                    0
% 2.36/1.03  res_moves_from_active_to_pass:          0
% 2.36/1.03  
% 2.36/1.03  ------ Superposition
% 2.36/1.03  
% 2.36/1.03  sup_time_total:                         0.
% 2.36/1.03  sup_time_generating:                    0.
% 2.36/1.03  sup_time_sim_full:                      0.
% 2.36/1.03  sup_time_sim_immed:                     0.
% 2.36/1.03  
% 2.36/1.03  sup_num_of_clauses:                     52
% 2.36/1.03  sup_num_in_active:                      28
% 2.36/1.03  sup_num_in_passive:                     24
% 2.36/1.03  sup_num_of_loops:                       58
% 2.36/1.03  sup_fw_superposition:                   45
% 2.36/1.03  sup_bw_superposition:                   55
% 2.36/1.03  sup_immediate_simplified:               19
% 2.36/1.03  sup_given_eliminated:                   0
% 2.36/1.03  comparisons_done:                       0
% 2.36/1.03  comparisons_avoided:                    0
% 2.36/1.03  
% 2.36/1.03  ------ Simplifications
% 2.36/1.03  
% 2.36/1.03  
% 2.36/1.03  sim_fw_subset_subsumed:                 9
% 2.36/1.03  sim_bw_subset_subsumed:                 10
% 2.36/1.03  sim_fw_subsumed:                        8
% 2.36/1.03  sim_bw_subsumed:                        0
% 2.36/1.03  sim_fw_subsumption_res:                 2
% 2.36/1.03  sim_bw_subsumption_res:                 0
% 2.36/1.03  sim_tautology_del:                      2
% 2.36/1.03  sim_eq_tautology_del:                   12
% 2.36/1.03  sim_eq_res_simp:                        0
% 2.36/1.03  sim_fw_demodulated:                     0
% 2.36/1.03  sim_bw_demodulated:                     30
% 2.36/1.03  sim_light_normalised:                   1
% 2.36/1.03  sim_joinable_taut:                      0
% 2.36/1.03  sim_joinable_simp:                      0
% 2.36/1.03  sim_ac_normalised:                      0
% 2.36/1.03  sim_smt_subsumption:                    0
% 2.36/1.03  
%------------------------------------------------------------------------------
