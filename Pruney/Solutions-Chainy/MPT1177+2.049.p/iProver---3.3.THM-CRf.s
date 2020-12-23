%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:57 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  180 (1488 expanded)
%              Number of clauses        :  113 ( 281 expanded)
%              Number of leaves         :   20 ( 490 expanded)
%              Depth                    :   21
%              Number of atoms          :  909 (14398 expanded)
%              Number of equality atoms :  169 ( 286 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f67,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f7])).

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
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
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
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f69,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1667,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_650,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_651,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_815,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_651,c_21])).

cnf(c_816,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_820,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_25,c_24,c_23,c_22])).

cnf(c_1118,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_820])).

cnf(c_1655,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_146,plain,
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

cnf(c_147,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_920,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_147,c_21])).

cnf(c_921,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_925,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_25,c_24,c_23,c_22])).

cnf(c_926,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_925])).

cnf(c_1661,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_1891,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1661])).

cnf(c_18,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_195,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_196,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_363,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_196])).

cnf(c_364,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_365,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1292,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1309,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1815,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1816,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_1969,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1998,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_944,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_945,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_25,c_24,c_23,c_22])).

cnf(c_1869,plain,
    ( ~ m1_orders_2(X0,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_2102,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_2103,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_1299,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1835,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X2 != sK4
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_1997,plain,
    ( m1_orders_2(X0,X1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X1 != sK1
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_2417,plain,
    ( m1_orders_2(sK4,X0,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X0 != sK1
    | sK4 != sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2419,plain,
    ( m1_orders_2(sK4,sK1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | sK4 != sK4
    | sK4 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1670,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1672,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1669,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2341,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1669])).

cnf(c_2787,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_2341])).

cnf(c_1668,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
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
    inference(cnf_transformation,[],[f60])).

cnf(c_578,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_579,plain,
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
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_860,plain,
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
    inference(resolution_lifted,[status(thm)],[c_579,c_21])).

cnf(c_861,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_865,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_25,c_24,c_23,c_22])).

cnf(c_1110,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_865])).

cnf(c_1657,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_2644,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1657])).

cnf(c_2910,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_2644])).

cnf(c_32,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_197,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_198,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_386,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_198])).

cnf(c_387,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_388,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_396,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_198])).

cnf(c_397,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_398,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1818,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1819,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_1983,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_2189,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_2190,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_1927,plain,
    ( ~ m1_orders_2(X0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_2261,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2265,plain,
    ( m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_2919,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2910,c_32,c_33,c_388,c_398,c_1819,c_2190,c_2265])).

cnf(c_2921,plain,
    ( m1_orders_2(sK3,sK1,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2919])).

cnf(c_1868,plain,
    ( ~ m1_orders_2(X0,sK1,sK4)
    | ~ m1_orders_2(sK4,sK1,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_2996,plain,
    ( ~ m1_orders_2(sK4,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_1300,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1840,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X2 != sK2
    | X0 != sK4
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_1968,plain,
    ( m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X0 != sK4
    | X1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_3340,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m2_orders_2(k1_xboole_0,X0,sK2)
    | X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_3341,plain,
    ( X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3340])).

cnf(c_3343,plain,
    ( sK2 != sK2
    | sK1 != sK1
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3341])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_617,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_618,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_836,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_618,c_21])).

cnf(c_837,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_841,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_837,c_25,c_24,c_23,c_22])).

cnf(c_1114,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_841])).

cnf(c_3433,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(k1_xboole_0,sK1,sK2)
    | ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_3439,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3433])).

cnf(c_3503,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1891,c_32,c_18,c_33,c_365,c_388,c_398,c_1309,c_1815,c_1816,c_1819,c_1969,c_1998,c_2103,c_2190,c_2265,c_2419,c_2787,c_2921,c_2996,c_3343,c_3439])).

cnf(c_3510,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1667,c_3503])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:32:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.28/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/0.99  
% 2.28/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.28/0.99  
% 2.28/0.99  ------  iProver source info
% 2.28/0.99  
% 2.28/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.28/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.28/0.99  git: non_committed_changes: false
% 2.28/0.99  git: last_make_outside_of_git: false
% 2.28/0.99  
% 2.28/0.99  ------ 
% 2.28/0.99  
% 2.28/0.99  ------ Input Options
% 2.28/0.99  
% 2.28/0.99  --out_options                           all
% 2.28/0.99  --tptp_safe_out                         true
% 2.28/0.99  --problem_path                          ""
% 2.28/0.99  --include_path                          ""
% 2.28/0.99  --clausifier                            res/vclausify_rel
% 2.28/0.99  --clausifier_options                    --mode clausify
% 2.28/0.99  --stdin                                 false
% 2.28/0.99  --stats_out                             all
% 2.28/0.99  
% 2.28/0.99  ------ General Options
% 2.28/0.99  
% 2.28/0.99  --fof                                   false
% 2.28/0.99  --time_out_real                         305.
% 2.28/0.99  --time_out_virtual                      -1.
% 2.28/0.99  --symbol_type_check                     false
% 2.28/0.99  --clausify_out                          false
% 2.28/0.99  --sig_cnt_out                           false
% 2.28/0.99  --trig_cnt_out                          false
% 2.28/0.99  --trig_cnt_out_tolerance                1.
% 2.28/0.99  --trig_cnt_out_sk_spl                   false
% 2.28/0.99  --abstr_cl_out                          false
% 2.28/0.99  
% 2.28/0.99  ------ Global Options
% 2.28/0.99  
% 2.28/0.99  --schedule                              default
% 2.28/0.99  --add_important_lit                     false
% 2.28/0.99  --prop_solver_per_cl                    1000
% 2.28/0.99  --min_unsat_core                        false
% 2.28/0.99  --soft_assumptions                      false
% 2.28/0.99  --soft_lemma_size                       3
% 2.28/0.99  --prop_impl_unit_size                   0
% 2.28/0.99  --prop_impl_unit                        []
% 2.28/0.99  --share_sel_clauses                     true
% 2.28/0.99  --reset_solvers                         false
% 2.28/0.99  --bc_imp_inh                            [conj_cone]
% 2.28/0.99  --conj_cone_tolerance                   3.
% 2.28/0.99  --extra_neg_conj                        none
% 2.28/0.99  --large_theory_mode                     true
% 2.28/0.99  --prolific_symb_bound                   200
% 2.28/0.99  --lt_threshold                          2000
% 2.28/0.99  --clause_weak_htbl                      true
% 2.28/0.99  --gc_record_bc_elim                     false
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing Options
% 2.28/0.99  
% 2.28/0.99  --preprocessing_flag                    true
% 2.28/0.99  --time_out_prep_mult                    0.1
% 2.28/0.99  --splitting_mode                        input
% 2.28/0.99  --splitting_grd                         true
% 2.28/0.99  --splitting_cvd                         false
% 2.28/0.99  --splitting_cvd_svl                     false
% 2.28/0.99  --splitting_nvd                         32
% 2.28/0.99  --sub_typing                            true
% 2.28/0.99  --prep_gs_sim                           true
% 2.28/0.99  --prep_unflatten                        true
% 2.28/0.99  --prep_res_sim                          true
% 2.28/0.99  --prep_upred                            true
% 2.28/0.99  --prep_sem_filter                       exhaustive
% 2.28/0.99  --prep_sem_filter_out                   false
% 2.28/0.99  --pred_elim                             true
% 2.28/0.99  --res_sim_input                         true
% 2.28/0.99  --eq_ax_congr_red                       true
% 2.28/0.99  --pure_diseq_elim                       true
% 2.28/0.99  --brand_transform                       false
% 2.28/0.99  --non_eq_to_eq                          false
% 2.28/0.99  --prep_def_merge                        true
% 2.28/0.99  --prep_def_merge_prop_impl              false
% 2.28/0.99  --prep_def_merge_mbd                    true
% 2.28/0.99  --prep_def_merge_tr_red                 false
% 2.28/0.99  --prep_def_merge_tr_cl                  false
% 2.28/0.99  --smt_preprocessing                     true
% 2.28/0.99  --smt_ac_axioms                         fast
% 2.28/0.99  --preprocessed_out                      false
% 2.28/0.99  --preprocessed_stats                    false
% 2.28/0.99  
% 2.28/0.99  ------ Abstraction refinement Options
% 2.28/0.99  
% 2.28/0.99  --abstr_ref                             []
% 2.28/0.99  --abstr_ref_prep                        false
% 2.28/0.99  --abstr_ref_until_sat                   false
% 2.28/0.99  --abstr_ref_sig_restrict                funpre
% 2.28/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.99  --abstr_ref_under                       []
% 2.28/0.99  
% 2.28/0.99  ------ SAT Options
% 2.28/0.99  
% 2.28/0.99  --sat_mode                              false
% 2.28/0.99  --sat_fm_restart_options                ""
% 2.28/0.99  --sat_gr_def                            false
% 2.28/0.99  --sat_epr_types                         true
% 2.28/0.99  --sat_non_cyclic_types                  false
% 2.28/0.99  --sat_finite_models                     false
% 2.28/0.99  --sat_fm_lemmas                         false
% 2.28/0.99  --sat_fm_prep                           false
% 2.28/0.99  --sat_fm_uc_incr                        true
% 2.28/0.99  --sat_out_model                         small
% 2.28/0.99  --sat_out_clauses                       false
% 2.28/0.99  
% 2.28/0.99  ------ QBF Options
% 2.28/0.99  
% 2.28/0.99  --qbf_mode                              false
% 2.28/0.99  --qbf_elim_univ                         false
% 2.28/0.99  --qbf_dom_inst                          none
% 2.28/0.99  --qbf_dom_pre_inst                      false
% 2.28/0.99  --qbf_sk_in                             false
% 2.28/0.99  --qbf_pred_elim                         true
% 2.28/0.99  --qbf_split                             512
% 2.28/0.99  
% 2.28/0.99  ------ BMC1 Options
% 2.28/0.99  
% 2.28/0.99  --bmc1_incremental                      false
% 2.28/0.99  --bmc1_axioms                           reachable_all
% 2.28/0.99  --bmc1_min_bound                        0
% 2.28/0.99  --bmc1_max_bound                        -1
% 2.28/0.99  --bmc1_max_bound_default                -1
% 2.28/0.99  --bmc1_symbol_reachability              true
% 2.28/0.99  --bmc1_property_lemmas                  false
% 2.28/0.99  --bmc1_k_induction                      false
% 2.28/0.99  --bmc1_non_equiv_states                 false
% 2.28/0.99  --bmc1_deadlock                         false
% 2.28/0.99  --bmc1_ucm                              false
% 2.28/0.99  --bmc1_add_unsat_core                   none
% 2.28/0.99  --bmc1_unsat_core_children              false
% 2.28/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.99  --bmc1_out_stat                         full
% 2.28/0.99  --bmc1_ground_init                      false
% 2.28/0.99  --bmc1_pre_inst_next_state              false
% 2.28/0.99  --bmc1_pre_inst_state                   false
% 2.28/0.99  --bmc1_pre_inst_reach_state             false
% 2.28/0.99  --bmc1_out_unsat_core                   false
% 2.28/0.99  --bmc1_aig_witness_out                  false
% 2.28/0.99  --bmc1_verbose                          false
% 2.28/0.99  --bmc1_dump_clauses_tptp                false
% 2.28/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.99  --bmc1_dump_file                        -
% 2.28/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.99  --bmc1_ucm_extend_mode                  1
% 2.28/0.99  --bmc1_ucm_init_mode                    2
% 2.28/0.99  --bmc1_ucm_cone_mode                    none
% 2.28/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.99  --bmc1_ucm_relax_model                  4
% 2.28/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.99  --bmc1_ucm_layered_model                none
% 2.28/0.99  --bmc1_ucm_max_lemma_size               10
% 2.28/0.99  
% 2.28/0.99  ------ AIG Options
% 2.28/0.99  
% 2.28/0.99  --aig_mode                              false
% 2.28/0.99  
% 2.28/0.99  ------ Instantiation Options
% 2.28/0.99  
% 2.28/0.99  --instantiation_flag                    true
% 2.28/0.99  --inst_sos_flag                         false
% 2.28/0.99  --inst_sos_phase                        true
% 2.28/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.99  --inst_lit_sel_side                     num_symb
% 2.28/0.99  --inst_solver_per_active                1400
% 2.28/0.99  --inst_solver_calls_frac                1.
% 2.28/0.99  --inst_passive_queue_type               priority_queues
% 2.28/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.99  --inst_passive_queues_freq              [25;2]
% 2.28/0.99  --inst_dismatching                      true
% 2.28/0.99  --inst_eager_unprocessed_to_passive     true
% 2.28/0.99  --inst_prop_sim_given                   true
% 2.28/0.99  --inst_prop_sim_new                     false
% 2.28/0.99  --inst_subs_new                         false
% 2.28/0.99  --inst_eq_res_simp                      false
% 2.28/0.99  --inst_subs_given                       false
% 2.28/0.99  --inst_orphan_elimination               true
% 2.28/0.99  --inst_learning_loop_flag               true
% 2.28/0.99  --inst_learning_start                   3000
% 2.28/0.99  --inst_learning_factor                  2
% 2.28/0.99  --inst_start_prop_sim_after_learn       3
% 2.28/0.99  --inst_sel_renew                        solver
% 2.28/0.99  --inst_lit_activity_flag                true
% 2.28/0.99  --inst_restr_to_given                   false
% 2.28/0.99  --inst_activity_threshold               500
% 2.28/0.99  --inst_out_proof                        true
% 2.28/0.99  
% 2.28/0.99  ------ Resolution Options
% 2.28/0.99  
% 2.28/0.99  --resolution_flag                       true
% 2.28/0.99  --res_lit_sel                           adaptive
% 2.28/0.99  --res_lit_sel_side                      none
% 2.28/0.99  --res_ordering                          kbo
% 2.28/0.99  --res_to_prop_solver                    active
% 2.28/0.99  --res_prop_simpl_new                    false
% 2.28/0.99  --res_prop_simpl_given                  true
% 2.28/0.99  --res_passive_queue_type                priority_queues
% 2.28/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.99  --res_passive_queues_freq               [15;5]
% 2.28/0.99  --res_forward_subs                      full
% 2.28/0.99  --res_backward_subs                     full
% 2.28/0.99  --res_forward_subs_resolution           true
% 2.28/0.99  --res_backward_subs_resolution          true
% 2.28/0.99  --res_orphan_elimination                true
% 2.28/0.99  --res_time_limit                        2.
% 2.28/0.99  --res_out_proof                         true
% 2.28/0.99  
% 2.28/0.99  ------ Superposition Options
% 2.28/0.99  
% 2.28/0.99  --superposition_flag                    true
% 2.28/0.99  --sup_passive_queue_type                priority_queues
% 2.28/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.99  --demod_completeness_check              fast
% 2.28/0.99  --demod_use_ground                      true
% 2.28/0.99  --sup_to_prop_solver                    passive
% 2.28/0.99  --sup_prop_simpl_new                    true
% 2.28/0.99  --sup_prop_simpl_given                  true
% 2.28/0.99  --sup_fun_splitting                     false
% 2.28/0.99  --sup_smt_interval                      50000
% 2.28/0.99  
% 2.28/0.99  ------ Superposition Simplification Setup
% 2.28/0.99  
% 2.28/0.99  --sup_indices_passive                   []
% 2.28/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_full_bw                           [BwDemod]
% 2.28/0.99  --sup_immed_triv                        [TrivRules]
% 2.28/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_immed_bw_main                     []
% 2.28/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.99  
% 2.28/0.99  ------ Combination Options
% 2.28/0.99  
% 2.28/0.99  --comb_res_mult                         3
% 2.28/0.99  --comb_sup_mult                         2
% 2.28/0.99  --comb_inst_mult                        10
% 2.28/0.99  
% 2.28/0.99  ------ Debug Options
% 2.28/0.99  
% 2.28/0.99  --dbg_backtrace                         false
% 2.28/0.99  --dbg_dump_prop_clauses                 false
% 2.28/0.99  --dbg_dump_prop_clauses_file            -
% 2.28/0.99  --dbg_out_stat                          false
% 2.28/0.99  ------ Parsing...
% 2.28/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.28/0.99  ------ Proving...
% 2.28/0.99  ------ Problem Properties 
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  clauses                                 19
% 2.28/0.99  conjectures                             2
% 2.28/0.99  EPR                                     13
% 2.28/0.99  Horn                                    15
% 2.28/0.99  unary                                   3
% 2.28/0.99  binary                                  7
% 2.28/0.99  lits                                    49
% 2.28/0.99  lits eq                                 6
% 2.28/0.99  fd_pure                                 0
% 2.28/0.99  fd_pseudo                               0
% 2.28/0.99  fd_cond                                 1
% 2.28/0.99  fd_pseudo_cond                          3
% 2.28/0.99  AC symbols                              0
% 2.28/0.99  
% 2.28/0.99  ------ Schedule dynamic 5 is on 
% 2.28/0.99  
% 2.28/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  ------ 
% 2.28/0.99  Current options:
% 2.28/0.99  ------ 
% 2.28/0.99  
% 2.28/0.99  ------ Input Options
% 2.28/0.99  
% 2.28/0.99  --out_options                           all
% 2.28/0.99  --tptp_safe_out                         true
% 2.28/0.99  --problem_path                          ""
% 2.28/0.99  --include_path                          ""
% 2.28/0.99  --clausifier                            res/vclausify_rel
% 2.28/0.99  --clausifier_options                    --mode clausify
% 2.28/0.99  --stdin                                 false
% 2.28/0.99  --stats_out                             all
% 2.28/0.99  
% 2.28/0.99  ------ General Options
% 2.28/0.99  
% 2.28/0.99  --fof                                   false
% 2.28/0.99  --time_out_real                         305.
% 2.28/0.99  --time_out_virtual                      -1.
% 2.28/0.99  --symbol_type_check                     false
% 2.28/0.99  --clausify_out                          false
% 2.28/0.99  --sig_cnt_out                           false
% 2.28/0.99  --trig_cnt_out                          false
% 2.28/0.99  --trig_cnt_out_tolerance                1.
% 2.28/0.99  --trig_cnt_out_sk_spl                   false
% 2.28/0.99  --abstr_cl_out                          false
% 2.28/0.99  
% 2.28/0.99  ------ Global Options
% 2.28/0.99  
% 2.28/0.99  --schedule                              default
% 2.28/0.99  --add_important_lit                     false
% 2.28/0.99  --prop_solver_per_cl                    1000
% 2.28/0.99  --min_unsat_core                        false
% 2.28/0.99  --soft_assumptions                      false
% 2.28/0.99  --soft_lemma_size                       3
% 2.28/0.99  --prop_impl_unit_size                   0
% 2.28/0.99  --prop_impl_unit                        []
% 2.28/0.99  --share_sel_clauses                     true
% 2.28/0.99  --reset_solvers                         false
% 2.28/0.99  --bc_imp_inh                            [conj_cone]
% 2.28/0.99  --conj_cone_tolerance                   3.
% 2.28/0.99  --extra_neg_conj                        none
% 2.28/0.99  --large_theory_mode                     true
% 2.28/0.99  --prolific_symb_bound                   200
% 2.28/0.99  --lt_threshold                          2000
% 2.28/0.99  --clause_weak_htbl                      true
% 2.28/0.99  --gc_record_bc_elim                     false
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing Options
% 2.28/0.99  
% 2.28/0.99  --preprocessing_flag                    true
% 2.28/0.99  --time_out_prep_mult                    0.1
% 2.28/0.99  --splitting_mode                        input
% 2.28/0.99  --splitting_grd                         true
% 2.28/0.99  --splitting_cvd                         false
% 2.28/0.99  --splitting_cvd_svl                     false
% 2.28/0.99  --splitting_nvd                         32
% 2.28/0.99  --sub_typing                            true
% 2.28/0.99  --prep_gs_sim                           true
% 2.28/0.99  --prep_unflatten                        true
% 2.28/0.99  --prep_res_sim                          true
% 2.28/0.99  --prep_upred                            true
% 2.28/0.99  --prep_sem_filter                       exhaustive
% 2.28/0.99  --prep_sem_filter_out                   false
% 2.28/0.99  --pred_elim                             true
% 2.28/0.99  --res_sim_input                         true
% 2.28/0.99  --eq_ax_congr_red                       true
% 2.28/0.99  --pure_diseq_elim                       true
% 2.28/0.99  --brand_transform                       false
% 2.28/0.99  --non_eq_to_eq                          false
% 2.28/0.99  --prep_def_merge                        true
% 2.28/0.99  --prep_def_merge_prop_impl              false
% 2.28/0.99  --prep_def_merge_mbd                    true
% 2.28/0.99  --prep_def_merge_tr_red                 false
% 2.28/0.99  --prep_def_merge_tr_cl                  false
% 2.28/0.99  --smt_preprocessing                     true
% 2.28/0.99  --smt_ac_axioms                         fast
% 2.28/0.99  --preprocessed_out                      false
% 2.28/0.99  --preprocessed_stats                    false
% 2.28/0.99  
% 2.28/0.99  ------ Abstraction refinement Options
% 2.28/0.99  
% 2.28/0.99  --abstr_ref                             []
% 2.28/0.99  --abstr_ref_prep                        false
% 2.28/0.99  --abstr_ref_until_sat                   false
% 2.28/0.99  --abstr_ref_sig_restrict                funpre
% 2.28/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.99  --abstr_ref_under                       []
% 2.28/0.99  
% 2.28/0.99  ------ SAT Options
% 2.28/0.99  
% 2.28/0.99  --sat_mode                              false
% 2.28/0.99  --sat_fm_restart_options                ""
% 2.28/0.99  --sat_gr_def                            false
% 2.28/0.99  --sat_epr_types                         true
% 2.28/0.99  --sat_non_cyclic_types                  false
% 2.28/0.99  --sat_finite_models                     false
% 2.28/0.99  --sat_fm_lemmas                         false
% 2.28/0.99  --sat_fm_prep                           false
% 2.28/0.99  --sat_fm_uc_incr                        true
% 2.28/0.99  --sat_out_model                         small
% 2.28/0.99  --sat_out_clauses                       false
% 2.28/0.99  
% 2.28/0.99  ------ QBF Options
% 2.28/0.99  
% 2.28/0.99  --qbf_mode                              false
% 2.28/0.99  --qbf_elim_univ                         false
% 2.28/0.99  --qbf_dom_inst                          none
% 2.28/0.99  --qbf_dom_pre_inst                      false
% 2.28/0.99  --qbf_sk_in                             false
% 2.28/0.99  --qbf_pred_elim                         true
% 2.28/0.99  --qbf_split                             512
% 2.28/0.99  
% 2.28/0.99  ------ BMC1 Options
% 2.28/0.99  
% 2.28/0.99  --bmc1_incremental                      false
% 2.28/0.99  --bmc1_axioms                           reachable_all
% 2.28/0.99  --bmc1_min_bound                        0
% 2.28/0.99  --bmc1_max_bound                        -1
% 2.28/0.99  --bmc1_max_bound_default                -1
% 2.28/0.99  --bmc1_symbol_reachability              true
% 2.28/0.99  --bmc1_property_lemmas                  false
% 2.28/0.99  --bmc1_k_induction                      false
% 2.28/0.99  --bmc1_non_equiv_states                 false
% 2.28/0.99  --bmc1_deadlock                         false
% 2.28/0.99  --bmc1_ucm                              false
% 2.28/0.99  --bmc1_add_unsat_core                   none
% 2.28/0.99  --bmc1_unsat_core_children              false
% 2.28/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.99  --bmc1_out_stat                         full
% 2.28/0.99  --bmc1_ground_init                      false
% 2.28/0.99  --bmc1_pre_inst_next_state              false
% 2.28/0.99  --bmc1_pre_inst_state                   false
% 2.28/0.99  --bmc1_pre_inst_reach_state             false
% 2.28/0.99  --bmc1_out_unsat_core                   false
% 2.28/0.99  --bmc1_aig_witness_out                  false
% 2.28/0.99  --bmc1_verbose                          false
% 2.28/0.99  --bmc1_dump_clauses_tptp                false
% 2.28/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.99  --bmc1_dump_file                        -
% 2.28/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.99  --bmc1_ucm_extend_mode                  1
% 2.28/0.99  --bmc1_ucm_init_mode                    2
% 2.28/0.99  --bmc1_ucm_cone_mode                    none
% 2.28/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.99  --bmc1_ucm_relax_model                  4
% 2.28/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.99  --bmc1_ucm_layered_model                none
% 2.28/0.99  --bmc1_ucm_max_lemma_size               10
% 2.28/0.99  
% 2.28/0.99  ------ AIG Options
% 2.28/0.99  
% 2.28/0.99  --aig_mode                              false
% 2.28/0.99  
% 2.28/0.99  ------ Instantiation Options
% 2.28/0.99  
% 2.28/0.99  --instantiation_flag                    true
% 2.28/0.99  --inst_sos_flag                         false
% 2.28/0.99  --inst_sos_phase                        true
% 2.28/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.99  --inst_lit_sel_side                     none
% 2.28/0.99  --inst_solver_per_active                1400
% 2.28/0.99  --inst_solver_calls_frac                1.
% 2.28/0.99  --inst_passive_queue_type               priority_queues
% 2.28/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.99  --inst_passive_queues_freq              [25;2]
% 2.28/0.99  --inst_dismatching                      true
% 2.28/0.99  --inst_eager_unprocessed_to_passive     true
% 2.28/0.99  --inst_prop_sim_given                   true
% 2.28/0.99  --inst_prop_sim_new                     false
% 2.28/0.99  --inst_subs_new                         false
% 2.28/0.99  --inst_eq_res_simp                      false
% 2.28/0.99  --inst_subs_given                       false
% 2.28/0.99  --inst_orphan_elimination               true
% 2.28/0.99  --inst_learning_loop_flag               true
% 2.28/0.99  --inst_learning_start                   3000
% 2.28/0.99  --inst_learning_factor                  2
% 2.28/0.99  --inst_start_prop_sim_after_learn       3
% 2.28/0.99  --inst_sel_renew                        solver
% 2.28/0.99  --inst_lit_activity_flag                true
% 2.28/0.99  --inst_restr_to_given                   false
% 2.28/0.99  --inst_activity_threshold               500
% 2.28/0.99  --inst_out_proof                        true
% 2.28/0.99  
% 2.28/0.99  ------ Resolution Options
% 2.28/0.99  
% 2.28/0.99  --resolution_flag                       false
% 2.28/0.99  --res_lit_sel                           adaptive
% 2.28/0.99  --res_lit_sel_side                      none
% 2.28/0.99  --res_ordering                          kbo
% 2.28/0.99  --res_to_prop_solver                    active
% 2.28/0.99  --res_prop_simpl_new                    false
% 2.28/0.99  --res_prop_simpl_given                  true
% 2.28/0.99  --res_passive_queue_type                priority_queues
% 2.28/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.99  --res_passive_queues_freq               [15;5]
% 2.28/0.99  --res_forward_subs                      full
% 2.28/0.99  --res_backward_subs                     full
% 2.28/0.99  --res_forward_subs_resolution           true
% 2.28/0.99  --res_backward_subs_resolution          true
% 2.28/0.99  --res_orphan_elimination                true
% 2.28/0.99  --res_time_limit                        2.
% 2.28/0.99  --res_out_proof                         true
% 2.28/0.99  
% 2.28/0.99  ------ Superposition Options
% 2.28/0.99  
% 2.28/0.99  --superposition_flag                    true
% 2.28/0.99  --sup_passive_queue_type                priority_queues
% 2.28/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.99  --demod_completeness_check              fast
% 2.28/0.99  --demod_use_ground                      true
% 2.28/0.99  --sup_to_prop_solver                    passive
% 2.28/0.99  --sup_prop_simpl_new                    true
% 2.28/0.99  --sup_prop_simpl_given                  true
% 2.28/0.99  --sup_fun_splitting                     false
% 2.28/0.99  --sup_smt_interval                      50000
% 2.28/0.99  
% 2.28/0.99  ------ Superposition Simplification Setup
% 2.28/0.99  
% 2.28/0.99  --sup_indices_passive                   []
% 2.28/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_full_bw                           [BwDemod]
% 2.28/0.99  --sup_immed_triv                        [TrivRules]
% 2.28/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_immed_bw_main                     []
% 2.28/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.99  
% 2.28/0.99  ------ Combination Options
% 2.28/0.99  
% 2.28/0.99  --comb_res_mult                         3
% 2.28/0.99  --comb_sup_mult                         2
% 2.28/0.99  --comb_inst_mult                        10
% 2.28/0.99  
% 2.28/0.99  ------ Debug Options
% 2.28/0.99  
% 2.28/0.99  --dbg_backtrace                         false
% 2.28/0.99  --dbg_dump_prop_clauses                 false
% 2.28/0.99  --dbg_dump_prop_clauses_file            -
% 2.28/0.99  --dbg_out_stat                          false
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  ------ Proving...
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  % SZS status Theorem for theBenchmark.p
% 2.28/0.99  
% 2.28/0.99   Resolution empty clause
% 2.28/0.99  
% 2.28/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.28/0.99  
% 2.28/0.99  fof(f12,conjecture,(
% 2.28/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f13,negated_conjecture,(
% 2.28/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.28/0.99    inference(negated_conjecture,[],[f12])).
% 2.28/0.99  
% 2.28/0.99  fof(f31,plain,(
% 2.28/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f13])).
% 2.28/0.99  
% 2.28/0.99  fof(f32,plain,(
% 2.28/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f31])).
% 2.28/0.99  
% 2.28/0.99  fof(f38,plain,(
% 2.28/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.28/0.99    inference(nnf_transformation,[],[f32])).
% 2.28/0.99  
% 2.28/0.99  fof(f39,plain,(
% 2.28/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f38])).
% 2.28/0.99  
% 2.28/0.99  fof(f43,plain,(
% 2.28/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 2.28/0.99    introduced(choice_axiom,[])).
% 2.28/0.99  
% 2.28/0.99  fof(f42,plain,(
% 2.28/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 2.28/0.99    introduced(choice_axiom,[])).
% 2.28/0.99  
% 2.28/0.99  fof(f41,plain,(
% 2.28/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 2.28/0.99    introduced(choice_axiom,[])).
% 2.28/0.99  
% 2.28/0.99  fof(f40,plain,(
% 2.28/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.28/0.99    introduced(choice_axiom,[])).
% 2.28/0.99  
% 2.28/0.99  fof(f44,plain,(
% 2.28/0.99    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.28/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f43,f42,f41,f40])).
% 2.28/0.99  
% 2.28/0.99  fof(f67,plain,(
% 2.28/0.99    m2_orders_2(sK3,sK1,sK2)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f7,axiom,(
% 2.28/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f15,plain,(
% 2.28/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.28/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.28/0.99  
% 2.28/0.99  fof(f21,plain,(
% 2.28/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f15])).
% 2.28/0.99  
% 2.28/0.99  fof(f22,plain,(
% 2.28/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f21])).
% 2.28/0.99  
% 2.28/0.99  fof(f55,plain,(
% 2.28/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f22])).
% 2.28/0.99  
% 2.28/0.99  fof(f66,plain,(
% 2.28/0.99    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f65,plain,(
% 2.28/0.99    l1_orders_2(sK1)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f61,plain,(
% 2.28/0.99    ~v2_struct_0(sK1)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f62,plain,(
% 2.28/0.99    v3_orders_2(sK1)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f63,plain,(
% 2.28/0.99    v4_orders_2(sK1)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f64,plain,(
% 2.28/0.99    v5_orders_2(sK1)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f9,axiom,(
% 2.28/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f25,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f9])).
% 2.28/0.99  
% 2.28/0.99  fof(f26,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f25])).
% 2.28/0.99  
% 2.28/0.99  fof(f57,plain,(
% 2.28/0.99    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f26])).
% 2.28/0.99  
% 2.28/0.99  fof(f6,axiom,(
% 2.28/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f19,plain,(
% 2.28/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f6])).
% 2.28/0.99  
% 2.28/0.99  fof(f20,plain,(
% 2.28/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f19])).
% 2.28/0.99  
% 2.28/0.99  fof(f54,plain,(
% 2.28/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f20])).
% 2.28/0.99  
% 2.28/0.99  fof(f68,plain,(
% 2.28/0.99    m2_orders_2(sK4,sK1,sK2)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f1,axiom,(
% 2.28/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f33,plain,(
% 2.28/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.28/0.99    inference(nnf_transformation,[],[f1])).
% 2.28/0.99  
% 2.28/0.99  fof(f34,plain,(
% 2.28/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.28/0.99    inference(flattening,[],[f33])).
% 2.28/0.99  
% 2.28/0.99  fof(f47,plain,(
% 2.28/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f34])).
% 2.28/0.99  
% 2.28/0.99  fof(f70,plain,(
% 2.28/0.99    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f8,axiom,(
% 2.28/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f23,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f8])).
% 2.28/0.99  
% 2.28/0.99  fof(f24,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f23])).
% 2.28/0.99  
% 2.28/0.99  fof(f56,plain,(
% 2.28/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f24])).
% 2.28/0.99  
% 2.28/0.99  fof(f3,axiom,(
% 2.28/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f51,plain,(
% 2.28/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f3])).
% 2.28/0.99  
% 2.28/0.99  fof(f2,axiom,(
% 2.28/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f14,plain,(
% 2.28/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.28/0.99    inference(rectify,[],[f2])).
% 2.28/0.99  
% 2.28/0.99  fof(f16,plain,(
% 2.28/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.28/0.99    inference(ennf_transformation,[],[f14])).
% 2.28/0.99  
% 2.28/0.99  fof(f35,plain,(
% 2.28/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.28/0.99    introduced(choice_axiom,[])).
% 2.28/0.99  
% 2.28/0.99  fof(f36,plain,(
% 2.28/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.28/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f35])).
% 2.28/0.99  
% 2.28/0.99  fof(f49,plain,(
% 2.28/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f36])).
% 2.28/0.99  
% 2.28/0.99  fof(f5,axiom,(
% 2.28/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f18,plain,(
% 2.28/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.28/0.99    inference(ennf_transformation,[],[f5])).
% 2.28/0.99  
% 2.28/0.99  fof(f53,plain,(
% 2.28/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f18])).
% 2.28/0.99  
% 2.28/0.99  fof(f11,axiom,(
% 2.28/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f29,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f11])).
% 2.28/0.99  
% 2.28/0.99  fof(f30,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f29])).
% 2.28/0.99  
% 2.28/0.99  fof(f37,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(nnf_transformation,[],[f30])).
% 2.28/0.99  
% 2.28/0.99  fof(f60,plain,(
% 2.28/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f37])).
% 2.28/0.99  
% 2.28/0.99  fof(f46,plain,(
% 2.28/0.99    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f34])).
% 2.28/0.99  
% 2.28/0.99  fof(f71,plain,(
% 2.28/0.99    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.28/0.99    inference(equality_resolution,[],[f46])).
% 2.28/0.99  
% 2.28/0.99  fof(f69,plain,(
% 2.28/0.99    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 2.28/0.99    inference(cnf_transformation,[],[f44])).
% 2.28/0.99  
% 2.28/0.99  fof(f4,axiom,(
% 2.28/0.99    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f17,plain,(
% 2.28/0.99    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.28/0.99    inference(ennf_transformation,[],[f4])).
% 2.28/0.99  
% 2.28/0.99  fof(f52,plain,(
% 2.28/0.99    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f17])).
% 2.28/0.99  
% 2.28/0.99  fof(f10,axiom,(
% 2.28/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.28/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.28/0.99  
% 2.28/0.99  fof(f27,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.28/0.99    inference(ennf_transformation,[],[f10])).
% 2.28/0.99  
% 2.28/0.99  fof(f28,plain,(
% 2.28/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.28/0.99    inference(flattening,[],[f27])).
% 2.28/0.99  
% 2.28/0.99  fof(f58,plain,(
% 2.28/0.99    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.28/0.99    inference(cnf_transformation,[],[f28])).
% 2.28/0.99  
% 2.28/0.99  cnf(c_19,negated_conjecture,
% 2.28/0.99      ( m2_orders_2(sK3,sK1,sK2) ),
% 2.28/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1667,plain,
% 2.28/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_10,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_20,negated_conjecture,
% 2.28/0.99      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 2.28/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_650,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK2 != X2 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_651,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_650]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_21,negated_conjecture,
% 2.28/0.99      ( l1_orders_2(sK1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_815,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK1 != X1 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_651,c_21]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_816,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | v2_struct_0(sK1)
% 2.28/0.99      | ~ v3_orders_2(sK1)
% 2.28/0.99      | ~ v4_orders_2(sK1)
% 2.28/0.99      | ~ v5_orders_2(sK1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_815]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_25,negated_conjecture,
% 2.28/0.99      ( ~ v2_struct_0(sK1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_24,negated_conjecture,
% 2.28/0.99      ( v3_orders_2(sK1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_23,negated_conjecture,
% 2.28/0.99      ( v4_orders_2(sK1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_22,negated_conjecture,
% 2.28/0.99      ( v5_orders_2(sK1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_820,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_816,c_25,c_24,c_23,c_22]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1118,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.28/0.99      inference(equality_resolution_simp,[status(thm)],[c_820]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1655,plain,
% 2.28/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_12,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_xboole_0 = X2 ),
% 2.28/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_9,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_146,plain,
% 2.28/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.28/0.99      | ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_xboole_0 = X2 ),
% 2.28/0.99      inference(global_propositional_subsumption,[status(thm)],[c_12,c_9]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_147,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_xboole_0 = X2 ),
% 2.28/0.99      inference(renaming,[status(thm)],[c_146]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_920,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_orders_2(X2,X1,X0)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | sK1 != X1
% 2.28/0.99      | k1_xboole_0 = X2 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_147,c_21]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_921,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | v2_struct_0(sK1)
% 2.28/0.99      | ~ v3_orders_2(sK1)
% 2.28/0.99      | ~ v4_orders_2(sK1)
% 2.28/0.99      | ~ v5_orders_2(sK1)
% 2.28/0.99      | k1_xboole_0 = X0 ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_920]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_925,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | k1_xboole_0 = X0 ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_921,c_25,c_24,c_23,c_22]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_926,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | k1_xboole_0 = X1 ),
% 2.28/0.99      inference(renaming,[status(thm)],[c_925]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1661,plain,
% 2.28/0.99      ( k1_xboole_0 = X0
% 2.28/0.99      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.28/0.99      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.28/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1891,plain,
% 2.28/0.99      ( k1_xboole_0 = X0
% 2.28/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.28/0.99      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1655,c_1661]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_18,negated_conjecture,
% 2.28/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 2.28/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_33,plain,
% 2.28/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_0,plain,
% 2.28/0.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.28/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_16,negated_conjecture,
% 2.28/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.28/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_195,plain,
% 2.28/0.99      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 2.28/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_196,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.28/0.99      inference(renaming,[status(thm)],[c_195]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_363,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | ~ r1_tarski(X0,X1)
% 2.28/0.99      | X1 = X0
% 2.28/0.99      | sK4 != X1
% 2.28/0.99      | sK3 != X0 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_196]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_364,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_363]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_365,plain,
% 2.28/0.99      ( sK4 = sK3
% 2.28/0.99      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.28/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1292,plain,( X0 = X0 ),theory(equality) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1309,plain,
% 2.28/0.99      ( sK1 = sK1 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1292]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1815,plain,
% 2.28/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1816,plain,
% 2.28/0.99      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_1815]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1969,plain,
% 2.28/0.99      ( sK2 = sK2 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1292]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1998,plain,
% 2.28/0.99      ( sK4 = sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1292]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_11,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | r1_tarski(X0,X2)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_944,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.28/0.99      | r1_tarski(X0,X2)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | sK1 != X1 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_945,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(X0,X1)
% 2.28/0.99      | v2_struct_0(sK1)
% 2.28/0.99      | ~ v3_orders_2(sK1)
% 2.28/0.99      | ~ v4_orders_2(sK1)
% 2.28/0.99      | ~ v5_orders_2(sK1) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_944]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_949,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(X0,X1) ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_945,c_25,c_24,c_23,c_22]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1869,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,sK4)
% 2.28/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(X0,sK4) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2102,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(sK3,sK4) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1869]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2103,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.28/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.28/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1299,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 2.28/0.99      | m1_orders_2(X3,X4,X5)
% 2.28/0.99      | X3 != X0
% 2.28/0.99      | X4 != X1
% 2.28/0.99      | X5 != X2 ),
% 2.28/0.99      theory(equality) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1835,plain,
% 2.28/0.99      ( m1_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | X2 != sK4
% 2.28/0.99      | X1 != sK1
% 2.28/0.99      | X0 != sK3 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1299]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1997,plain,
% 2.28/0.99      ( m1_orders_2(X0,X1,sK4)
% 2.28/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | X1 != sK1
% 2.28/0.99      | X0 != sK3
% 2.28/0.99      | sK4 != sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1835]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2417,plain,
% 2.28/0.99      ( m1_orders_2(sK4,X0,sK4)
% 2.28/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | X0 != sK1
% 2.28/0.99      | sK4 != sK4
% 2.28/0.99      | sK4 != sK3 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1997]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2419,plain,
% 2.28/0.99      ( m1_orders_2(sK4,sK1,sK4)
% 2.28/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | sK4 != sK4
% 2.28/0.99      | sK4 != sK3
% 2.28/0.99      | sK1 != sK1 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_2417]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_6,plain,
% 2.28/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.28/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1670,plain,
% 2.28/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_4,plain,
% 2.28/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1672,plain,
% 2.28/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.28/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_8,plain,
% 2.28/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.28/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1669,plain,
% 2.28/0.99      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2341,plain,
% 2.28/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 2.28/0.99      | r1_tarski(X1,sK0(X0,X1)) != iProver_top ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1672,c_1669]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2787,plain,
% 2.28/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1670,c_2341]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1668,plain,
% 2.28/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_14,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.28/0.99      | m1_orders_2(X3,X1,X0)
% 2.28/0.99      | m1_orders_2(X0,X1,X3)
% 2.28/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | X3 = X0 ),
% 2.28/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_578,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.28/0.99      | m1_orders_2(X3,X1,X0)
% 2.28/0.99      | m1_orders_2(X0,X1,X3)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | X3 = X0
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK2 != X2 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_579,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 2.28/0.99      | m1_orders_2(X0,X1,X2)
% 2.28/0.99      | m1_orders_2(X2,X1,X0)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | X0 = X2
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_578]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_860,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 2.28/0.99      | m1_orders_2(X0,X1,X2)
% 2.28/0.99      | m1_orders_2(X2,X1,X0)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | X2 = X0
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK1 != X1 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_579,c_21]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_861,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | v2_struct_0(sK1)
% 2.28/0.99      | ~ v3_orders_2(sK1)
% 2.28/0.99      | ~ v4_orders_2(sK1)
% 2.28/0.99      | ~ v5_orders_2(sK1)
% 2.28/0.99      | X1 = X0
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_860]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_865,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | X1 = X0
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_861,c_25,c_24,c_23,c_22]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1110,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | m1_orders_2(X1,sK1,X0)
% 2.28/0.99      | m1_orders_2(X0,sK1,X1)
% 2.28/0.99      | X1 = X0 ),
% 2.28/0.99      inference(equality_resolution_simp,[status(thm)],[c_865]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1657,plain,
% 2.28/0.99      ( X0 = X1
% 2.28/0.99      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.28/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_orders_2(X0,sK1,X1) = iProver_top
% 2.28/0.99      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2644,plain,
% 2.28/0.99      ( sK4 = X0
% 2.28/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 2.28/0.99      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1668,c_1657]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2910,plain,
% 2.28/0.99      ( sK4 = sK3
% 2.28/0.99      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.28/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1667,c_2644]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_32,plain,
% 2.28/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1,plain,
% 2.28/0.99      ( ~ r2_xboole_0(X0,X0) ),
% 2.28/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_17,negated_conjecture,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.28/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_197,plain,
% 2.28/0.99      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 2.28/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_198,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.28/0.99      inference(renaming,[status(thm)],[c_197]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_386,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_198]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_387,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_388,plain,
% 2.28/0.99      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_7,plain,
% 2.28/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 2.28/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_396,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(X0,X1) | sK4 != X0 | sK3 != X1 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_198]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_397,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK4,sK3) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_398,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 2.28/0.99      | r1_tarski(sK4,sK3) != iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1818,plain,
% 2.28/0.99      ( ~ m2_orders_2(sK3,sK1,sK2)
% 2.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1118]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1819,plain,
% 2.28/0.99      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1983,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | m1_orders_2(X0,sK1,sK4)
% 2.28/0.99      | m1_orders_2(sK4,sK1,X0)
% 2.28/0.99      | X0 = sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2189,plain,
% 2.28/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(sK3,sK1,sK2)
% 2.28/0.99      | m1_orders_2(sK4,sK1,sK3)
% 2.28/0.99      | m1_orders_2(sK3,sK1,sK4)
% 2.28/0.99      | sK3 = sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1983]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2190,plain,
% 2.28/0.99      ( sK3 = sK4
% 2.28/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.28/0.99      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 2.28/0.99      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.28/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2189]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1927,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,sK3)
% 2.28/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(X0,sK3) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2261,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK4,sK1,sK3)
% 2.28/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | r1_tarski(sK4,sK3) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1927]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2265,plain,
% 2.28/0.99      ( m1_orders_2(sK4,sK1,sK3) != iProver_top
% 2.28/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.28/0.99      | r1_tarski(sK4,sK3) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_2261]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2919,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_2910,c_32,c_33,c_388,c_398,c_1819,c_2190,c_2265]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2921,plain,
% 2.28/0.99      ( m1_orders_2(sK3,sK1,sK4) ),
% 2.28/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2919]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1868,plain,
% 2.28/0.99      ( ~ m1_orders_2(X0,sK1,sK4)
% 2.28/0.99      | ~ m1_orders_2(sK4,sK1,X0)
% 2.28/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | k1_xboole_0 = sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_926]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_2996,plain,
% 2.28/0.99      ( ~ m1_orders_2(sK4,sK1,sK4)
% 2.28/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.28/0.99      | k1_xboole_0 = sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1868]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1300,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | m2_orders_2(X3,X4,X5)
% 2.28/0.99      | X3 != X0
% 2.28/0.99      | X4 != X1
% 2.28/0.99      | X5 != X2 ),
% 2.28/0.99      theory(equality) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1840,plain,
% 2.28/0.99      ( m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | X2 != sK2
% 2.28/0.99      | X0 != sK4
% 2.28/0.99      | X1 != sK1 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1968,plain,
% 2.28/0.99      ( m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | X0 != sK4
% 2.28/0.99      | X1 != sK1
% 2.28/0.99      | sK2 != sK2 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1840]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3340,plain,
% 2.28/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.28/0.99      | m2_orders_2(k1_xboole_0,X0,sK2)
% 2.28/0.99      | X0 != sK1
% 2.28/0.99      | sK2 != sK2
% 2.28/0.99      | k1_xboole_0 != sK4 ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3341,plain,
% 2.28/0.99      ( X0 != sK1
% 2.28/0.99      | sK2 != sK2
% 2.28/0.99      | k1_xboole_0 != sK4
% 2.28/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.28/0.99      | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_3340]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3343,plain,
% 2.28/0.99      ( sK2 != sK2
% 2.28/0.99      | sK1 != sK1
% 2.28/0.99      | k1_xboole_0 != sK4
% 2.28/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.28/0.99      | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_3341]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_13,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.28/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.28/0.99      | ~ r1_xboole_0(X0,X3)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1) ),
% 2.28/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_617,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 2.28/0.99      | ~ m2_orders_2(X3,X1,X2)
% 2.28/0.99      | ~ r1_xboole_0(X0,X3)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK2 != X2 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_618,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X2,X0)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | ~ l1_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_617]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_836,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X2,X1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X2,X0)
% 2.28/0.99      | v2_struct_0(X1)
% 2.28/0.99      | ~ v3_orders_2(X1)
% 2.28/0.99      | ~ v4_orders_2(X1)
% 2.28/0.99      | ~ v5_orders_2(X1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.28/0.99      | sK1 != X1 ),
% 2.28/0.99      inference(resolution_lifted,[status(thm)],[c_618,c_21]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_837,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X1,X0)
% 2.28/0.99      | v2_struct_0(sK1)
% 2.28/0.99      | ~ v3_orders_2(sK1)
% 2.28/0.99      | ~ v4_orders_2(sK1)
% 2.28/0.99      | ~ v5_orders_2(sK1)
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(unflattening,[status(thm)],[c_836]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_841,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X1,X0)
% 2.28/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_837,c_25,c_24,c_23,c_22]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_1114,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(X1,sK1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X1,X0) ),
% 2.28/0.99      inference(equality_resolution_simp,[status(thm)],[c_841]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3433,plain,
% 2.28/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.28/0.99      | ~ m2_orders_2(k1_xboole_0,sK1,sK2)
% 2.28/0.99      | ~ r1_xboole_0(X0,k1_xboole_0) ),
% 2.28/0.99      inference(instantiation,[status(thm)],[c_1114]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3439,plain,
% 2.28/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.28/0.99      | m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top
% 2.28/0.99      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 2.28/0.99      inference(predicate_to_equality,[status(thm)],[c_3433]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3503,plain,
% 2.28/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 2.28/0.99      inference(global_propositional_subsumption,
% 2.28/0.99                [status(thm)],
% 2.28/0.99                [c_1891,c_32,c_18,c_33,c_365,c_388,c_398,c_1309,c_1815,
% 2.28/0.99                 c_1816,c_1819,c_1969,c_1998,c_2103,c_2190,c_2265,c_2419,
% 2.28/0.99                 c_2787,c_2921,c_2996,c_3343,c_3439]) ).
% 2.28/0.99  
% 2.28/0.99  cnf(c_3510,plain,
% 2.28/0.99      ( $false ),
% 2.28/0.99      inference(superposition,[status(thm)],[c_1667,c_3503]) ).
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.28/0.99  
% 2.28/0.99  ------                               Statistics
% 2.28/0.99  
% 2.28/0.99  ------ General
% 2.28/0.99  
% 2.28/0.99  abstr_ref_over_cycles:                  0
% 2.28/0.99  abstr_ref_under_cycles:                 0
% 2.28/0.99  gc_basic_clause_elim:                   0
% 2.28/0.99  forced_gc_time:                         0
% 2.28/0.99  parsing_time:                           0.013
% 2.28/0.99  unif_index_cands_time:                  0.
% 2.28/0.99  unif_index_add_time:                    0.
% 2.28/0.99  orderings_time:                         0.
% 2.28/0.99  out_proof_time:                         0.013
% 2.28/0.99  total_time:                             0.147
% 2.28/0.99  num_of_symbols:                         53
% 2.28/0.99  num_of_terms:                           1676
% 2.28/0.99  
% 2.28/0.99  ------ Preprocessing
% 2.28/0.99  
% 2.28/0.99  num_of_splits:                          0
% 2.28/0.99  num_of_split_atoms:                     0
% 2.28/0.99  num_of_reused_defs:                     0
% 2.28/0.99  num_eq_ax_congr_red:                    19
% 2.28/0.99  num_of_sem_filtered_clauses:            1
% 2.28/0.99  num_of_subtypes:                        0
% 2.28/0.99  monotx_restored_types:                  0
% 2.28/0.99  sat_num_of_epr_types:                   0
% 2.28/0.99  sat_num_of_non_cyclic_types:            0
% 2.28/0.99  sat_guarded_non_collapsed_types:        0
% 2.28/0.99  num_pure_diseq_elim:                    0
% 2.28/0.99  simp_replaced_by:                       0
% 2.28/0.99  res_preprocessed:                       102
% 2.28/0.99  prep_upred:                             0
% 2.28/0.99  prep_unflattend:                        54
% 2.28/0.99  smt_new_axioms:                         0
% 2.28/0.99  pred_elim_cands:                        6
% 2.28/0.99  pred_elim:                              7
% 2.28/0.99  pred_elim_cl:                           7
% 2.28/0.99  pred_elim_cycles:                       11
% 2.28/0.99  merged_defs:                            2
% 2.28/0.99  merged_defs_ncl:                        0
% 2.28/0.99  bin_hyper_res:                          2
% 2.28/0.99  prep_cycles:                            4
% 2.28/0.99  pred_elim_time:                         0.018
% 2.28/0.99  splitting_time:                         0.
% 2.28/0.99  sem_filter_time:                        0.
% 2.28/0.99  monotx_time:                            0.001
% 2.28/0.99  subtype_inf_time:                       0.
% 2.28/0.99  
% 2.28/0.99  ------ Problem properties
% 2.28/0.99  
% 2.28/0.99  clauses:                                19
% 2.28/0.99  conjectures:                            2
% 2.28/0.99  epr:                                    13
% 2.28/0.99  horn:                                   15
% 2.28/0.99  ground:                                 6
% 2.28/0.99  unary:                                  3
% 2.28/0.99  binary:                                 7
% 2.28/0.99  lits:                                   49
% 2.28/0.99  lits_eq:                                6
% 2.28/0.99  fd_pure:                                0
% 2.28/0.99  fd_pseudo:                              0
% 2.28/0.99  fd_cond:                                1
% 2.28/0.99  fd_pseudo_cond:                         3
% 2.28/0.99  ac_symbols:                             0
% 2.28/0.99  
% 2.28/0.99  ------ Propositional Solver
% 2.28/0.99  
% 2.28/0.99  prop_solver_calls:                      28
% 2.28/0.99  prop_fast_solver_calls:                 927
% 2.28/0.99  smt_solver_calls:                       0
% 2.28/0.99  smt_fast_solver_calls:                  0
% 2.28/0.99  prop_num_of_clauses:                    982
% 2.28/0.99  prop_preprocess_simplified:             4019
% 2.28/0.99  prop_fo_subsumed:                       36
% 2.28/0.99  prop_solver_time:                       0.
% 2.28/0.99  smt_solver_time:                        0.
% 2.28/0.99  smt_fast_solver_time:                   0.
% 2.28/0.99  prop_fast_solver_time:                  0.
% 2.28/0.99  prop_unsat_core_time:                   0.
% 2.28/0.99  
% 2.28/0.99  ------ QBF
% 2.28/0.99  
% 2.28/0.99  qbf_q_res:                              0
% 2.28/0.99  qbf_num_tautologies:                    0
% 2.28/0.99  qbf_prep_cycles:                        0
% 2.28/0.99  
% 2.28/0.99  ------ BMC1
% 2.28/0.99  
% 2.28/0.99  bmc1_current_bound:                     -1
% 2.28/0.99  bmc1_last_solved_bound:                 -1
% 2.28/0.99  bmc1_unsat_core_size:                   -1
% 2.28/0.99  bmc1_unsat_core_parents_size:           -1
% 2.28/0.99  bmc1_merge_next_fun:                    0
% 2.28/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.28/0.99  
% 2.28/0.99  ------ Instantiation
% 2.28/0.99  
% 2.28/0.99  inst_num_of_clauses:                    267
% 2.28/0.99  inst_num_in_passive:                    40
% 2.28/0.99  inst_num_in_active:                     205
% 2.28/0.99  inst_num_in_unprocessed:                22
% 2.28/0.99  inst_num_of_loops:                      220
% 2.28/0.99  inst_num_of_learning_restarts:          0
% 2.28/0.99  inst_num_moves_active_passive:          11
% 2.28/0.99  inst_lit_activity:                      0
% 2.28/0.99  inst_lit_activity_moves:                0
% 2.28/0.99  inst_num_tautologies:                   0
% 2.28/0.99  inst_num_prop_implied:                  0
% 2.28/0.99  inst_num_existing_simplified:           0
% 2.28/0.99  inst_num_eq_res_simplified:             0
% 2.28/0.99  inst_num_child_elim:                    0
% 2.28/0.99  inst_num_of_dismatching_blockings:      14
% 2.28/0.99  inst_num_of_non_proper_insts:           217
% 2.28/0.99  inst_num_of_duplicates:                 0
% 2.28/0.99  inst_inst_num_from_inst_to_res:         0
% 2.28/0.99  inst_dismatching_checking_time:         0.
% 2.28/0.99  
% 2.28/0.99  ------ Resolution
% 2.28/0.99  
% 2.28/0.99  res_num_of_clauses:                     0
% 2.28/0.99  res_num_in_passive:                     0
% 2.28/0.99  res_num_in_active:                      0
% 2.28/0.99  res_num_of_loops:                       106
% 2.28/0.99  res_forward_subset_subsumed:            37
% 2.28/0.99  res_backward_subset_subsumed:           2
% 2.28/0.99  res_forward_subsumed:                   0
% 2.28/0.99  res_backward_subsumed:                  0
% 2.28/0.99  res_forward_subsumption_resolution:     0
% 2.28/0.99  res_backward_subsumption_resolution:    0
% 2.28/0.99  res_clause_to_clause_subsumption:       101
% 2.28/0.99  res_orphan_elimination:                 0
% 2.28/0.99  res_tautology_del:                      41
% 2.28/0.99  res_num_eq_res_simplified:              4
% 2.28/0.99  res_num_sel_changes:                    0
% 2.28/0.99  res_moves_from_active_to_pass:          0
% 2.28/0.99  
% 2.28/0.99  ------ Superposition
% 2.28/0.99  
% 2.28/0.99  sup_time_total:                         0.
% 2.28/0.99  sup_time_generating:                    0.
% 2.28/0.99  sup_time_sim_full:                      0.
% 2.28/0.99  sup_time_sim_immed:                     0.
% 2.28/0.99  
% 2.28/0.99  sup_num_of_clauses:                     34
% 2.28/0.99  sup_num_in_active:                      26
% 2.28/0.99  sup_num_in_passive:                     8
% 2.28/0.99  sup_num_of_loops:                       42
% 2.28/0.99  sup_fw_superposition:                   28
% 2.28/0.99  sup_bw_superposition:                   15
% 2.28/0.99  sup_immediate_simplified:               4
% 2.28/0.99  sup_given_eliminated:                   0
% 2.28/0.99  comparisons_done:                       0
% 2.28/0.99  comparisons_avoided:                    0
% 2.28/0.99  
% 2.28/0.99  ------ Simplifications
% 2.28/0.99  
% 2.28/0.99  
% 2.28/0.99  sim_fw_subset_subsumed:                 3
% 2.28/0.99  sim_bw_subset_subsumed:                 8
% 2.28/0.99  sim_fw_subsumed:                        1
% 2.28/0.99  sim_bw_subsumed:                        0
% 2.28/0.99  sim_fw_subsumption_res:                 0
% 2.28/0.99  sim_bw_subsumption_res:                 0
% 2.28/0.99  sim_tautology_del:                      1
% 2.28/0.99  sim_eq_tautology_del:                   3
% 2.28/0.99  sim_eq_res_simp:                        0
% 2.28/0.99  sim_fw_demodulated:                     0
% 2.28/0.99  sim_bw_demodulated:                     12
% 2.28/0.99  sim_light_normalised:                   1
% 2.28/0.99  sim_joinable_taut:                      0
% 2.28/0.99  sim_joinable_simp:                      0
% 2.28/0.99  sim_ac_normalised:                      0
% 2.28/0.99  sim_smt_subsumption:                    0
% 2.28/0.99  
%------------------------------------------------------------------------------
