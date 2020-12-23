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
% DateTime   : Thu Dec  3 12:12:57 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 915 expanded)
%              Number of clauses        :   89 ( 170 expanded)
%              Number of leaves         :   16 ( 298 expanded)
%              Depth                    :   19
%              Number of atoms          :  851 (8923 expanded)
%              Number of equality atoms :  105 ( 153 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( ( ~ m1_orders_2(X2,X0,sK4)
          | ~ r2_xboole_0(X2,sK4) )
        & ( m1_orders_2(X2,X0,sK4)
          | r2_xboole_0(X2,sK4) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
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
            ( ( ~ m1_orders_2(sK3,X0,X3)
              | ~ r2_xboole_0(sK3,X3) )
            & ( m1_orders_2(sK3,X0,X3)
              | r2_xboole_0(sK3,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
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
                & m2_orders_2(X3,X0,sK2) )
            & m2_orders_2(X2,X0,sK2) )
        & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))) ) ) ),
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f36,f35,f34,f33])).

fof(f59,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

fof(f54,plain,(
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

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
                    & r2_hidden(sK0(X0,X1,X2),X2)
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_965,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_966,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_970,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_26,c_25,c_24,c_23])).

cnf(c_1745,plain,
    ( ~ m1_orders_2(X0_55,sK1,X1_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_970])).

cnf(c_2397,plain,
    ( ~ m1_orders_2(X0_55,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_55,sK3) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_2716,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_1777,plain,
    ( ~ m1_orders_2(X0_55,X0_56,X1_55)
    | m1_orders_2(X2_55,X0_56,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_2371,plain,
    ( m1_orders_2(X0_55,sK1,X1_55)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X1_55 != sK4
    | X0_55 != sK3 ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_2477,plain,
    ( m1_orders_2(X0_55,sK1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X0_55 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_2704,plain,
    ( m1_orders_2(sK4,sK1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | sK4 != sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_2477])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_210,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_211,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_410,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_211])).

cnf(c_411,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1757,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_2161,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_21,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_412,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_986,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_987,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_989,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_26,c_25,c_24,c_23])).

cnf(c_1744,plain,
    ( ~ m2_orders_2(X0_55,sK1,X0_57)
    | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_989])).

cnf(c_2351,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_2352,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2351])).

cnf(c_2387,plain,
    ( ~ m1_orders_2(X0_55,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_55,sK4) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_2512,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_2513,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2512])).

cnf(c_2647,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2161,c_32,c_34,c_412,c_2352,c_2513])).

cnf(c_2649,plain,
    ( r1_tarski(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2647])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_918,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_919,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_921,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_26,c_25,c_24,c_23])).

cnf(c_922,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_921])).

cnf(c_1747,plain,
    ( m1_orders_2(X0_55,sK1,X1_55)
    | m1_orders_2(X1_55,sK1,X0_55)
    | ~ m2_orders_2(X0_55,sK1,X0_57)
    | ~ m2_orders_2(X1_55,sK1,X0_57)
    | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
    | X0_55 = X1_55 ),
    inference(subtyping,[status(esa)],[c_922])).

cnf(c_2423,plain,
    ( m1_orders_2(X0_55,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0_55)
    | ~ m2_orders_2(X0_55,sK1,X0_57)
    | ~ m2_orders_2(sK4,sK1,X0_57)
    | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
    | X0_55 = sK4 ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_2633,plain,
    ( m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_1766,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2478,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_944,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_945,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_26,c_25,c_24,c_23])).

cnf(c_1746,plain,
    ( ~ m1_orders_2(X0_55,sK1,X0_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_55 ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_2411,plain,
    ( ~ m1_orders_2(sK4,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1771,plain,
    ( ~ m2_orders_2(X0_55,X0_56,X0_57)
    | m2_orders_2(X1_55,X0_56,X0_57)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_2361,plain,
    ( m2_orders_2(X0_55,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X0_55 != sK4 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_2363,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m2_orders_2(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_2354,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_644,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(k1_xboole_0,X3,X4)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3)
    | X3 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_9])).

cnf(c_645,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_669,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_645,c_10])).

cnf(c_753,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_669,c_22])).

cnf(c_754,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_758,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_26,c_25,c_24,c_23])).

cnf(c_1754,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0_57)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1_57)
    | ~ m1_orders_1(X1_57,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_1763,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0_57)
    | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1754])).

cnf(c_1800,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_1764,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1754])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_420,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_211])).

cnf(c_421,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1756,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_208,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_209,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_397,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_209])).

cnf(c_398,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1758,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_430,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_211])).

cnf(c_431,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2716,c_2704,c_2649,c_2633,c_2478,c_2411,c_2363,c_2354,c_2351,c_1800,c_1764,c_1756,c_1758,c_431,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % WCLimit    : 600
% 0.19/0.33  % DateTime   : Tue Dec  1 18:08:42 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.43/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.43/0.99  
% 1.43/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.43/0.99  
% 1.43/0.99  ------  iProver source info
% 1.43/0.99  
% 1.43/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.43/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.43/0.99  git: non_committed_changes: false
% 1.43/0.99  git: last_make_outside_of_git: false
% 1.43/0.99  
% 1.43/0.99  ------ 
% 1.43/0.99  
% 1.43/0.99  ------ Input Options
% 1.43/0.99  
% 1.43/0.99  --out_options                           all
% 1.43/0.99  --tptp_safe_out                         true
% 1.43/0.99  --problem_path                          ""
% 1.43/0.99  --include_path                          ""
% 1.43/0.99  --clausifier                            res/vclausify_rel
% 1.43/0.99  --clausifier_options                    --mode clausify
% 1.43/0.99  --stdin                                 false
% 1.43/0.99  --stats_out                             all
% 1.43/0.99  
% 1.43/0.99  ------ General Options
% 1.43/0.99  
% 1.43/0.99  --fof                                   false
% 1.43/0.99  --time_out_real                         305.
% 1.43/0.99  --time_out_virtual                      -1.
% 1.43/0.99  --symbol_type_check                     false
% 1.43/0.99  --clausify_out                          false
% 1.43/0.99  --sig_cnt_out                           false
% 1.43/0.99  --trig_cnt_out                          false
% 1.43/0.99  --trig_cnt_out_tolerance                1.
% 1.43/0.99  --trig_cnt_out_sk_spl                   false
% 1.43/0.99  --abstr_cl_out                          false
% 1.43/0.99  
% 1.43/0.99  ------ Global Options
% 1.43/0.99  
% 1.43/0.99  --schedule                              default
% 1.43/0.99  --add_important_lit                     false
% 1.43/0.99  --prop_solver_per_cl                    1000
% 1.43/0.99  --min_unsat_core                        false
% 1.43/0.99  --soft_assumptions                      false
% 1.43/0.99  --soft_lemma_size                       3
% 1.43/0.99  --prop_impl_unit_size                   0
% 1.43/0.99  --prop_impl_unit                        []
% 1.43/0.99  --share_sel_clauses                     true
% 1.43/0.99  --reset_solvers                         false
% 1.43/0.99  --bc_imp_inh                            [conj_cone]
% 1.43/0.99  --conj_cone_tolerance                   3.
% 1.43/0.99  --extra_neg_conj                        none
% 1.43/0.99  --large_theory_mode                     true
% 1.43/0.99  --prolific_symb_bound                   200
% 1.43/0.99  --lt_threshold                          2000
% 1.43/0.99  --clause_weak_htbl                      true
% 1.43/0.99  --gc_record_bc_elim                     false
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing Options
% 1.43/0.99  
% 1.43/0.99  --preprocessing_flag                    true
% 1.43/0.99  --time_out_prep_mult                    0.1
% 1.43/0.99  --splitting_mode                        input
% 1.43/0.99  --splitting_grd                         true
% 1.43/0.99  --splitting_cvd                         false
% 1.43/0.99  --splitting_cvd_svl                     false
% 1.43/0.99  --splitting_nvd                         32
% 1.43/0.99  --sub_typing                            true
% 1.43/0.99  --prep_gs_sim                           true
% 1.43/0.99  --prep_unflatten                        true
% 1.43/0.99  --prep_res_sim                          true
% 1.43/0.99  --prep_upred                            true
% 1.43/0.99  --prep_sem_filter                       exhaustive
% 1.43/0.99  --prep_sem_filter_out                   false
% 1.43/0.99  --pred_elim                             true
% 1.43/0.99  --res_sim_input                         true
% 1.43/0.99  --eq_ax_congr_red                       true
% 1.43/0.99  --pure_diseq_elim                       true
% 1.43/0.99  --brand_transform                       false
% 1.43/0.99  --non_eq_to_eq                          false
% 1.43/0.99  --prep_def_merge                        true
% 1.43/0.99  --prep_def_merge_prop_impl              false
% 1.43/0.99  --prep_def_merge_mbd                    true
% 1.43/0.99  --prep_def_merge_tr_red                 false
% 1.43/0.99  --prep_def_merge_tr_cl                  false
% 1.43/0.99  --smt_preprocessing                     true
% 1.43/0.99  --smt_ac_axioms                         fast
% 1.43/0.99  --preprocessed_out                      false
% 1.43/0.99  --preprocessed_stats                    false
% 1.43/0.99  
% 1.43/0.99  ------ Abstraction refinement Options
% 1.43/0.99  
% 1.43/0.99  --abstr_ref                             []
% 1.43/0.99  --abstr_ref_prep                        false
% 1.43/0.99  --abstr_ref_until_sat                   false
% 1.43/0.99  --abstr_ref_sig_restrict                funpre
% 1.43/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.99  --abstr_ref_under                       []
% 1.43/0.99  
% 1.43/0.99  ------ SAT Options
% 1.43/0.99  
% 1.43/0.99  --sat_mode                              false
% 1.43/0.99  --sat_fm_restart_options                ""
% 1.43/0.99  --sat_gr_def                            false
% 1.43/0.99  --sat_epr_types                         true
% 1.43/0.99  --sat_non_cyclic_types                  false
% 1.43/0.99  --sat_finite_models                     false
% 1.43/0.99  --sat_fm_lemmas                         false
% 1.43/0.99  --sat_fm_prep                           false
% 1.43/0.99  --sat_fm_uc_incr                        true
% 1.43/0.99  --sat_out_model                         small
% 1.43/0.99  --sat_out_clauses                       false
% 1.43/0.99  
% 1.43/0.99  ------ QBF Options
% 1.43/0.99  
% 1.43/0.99  --qbf_mode                              false
% 1.43/0.99  --qbf_elim_univ                         false
% 1.43/0.99  --qbf_dom_inst                          none
% 1.43/0.99  --qbf_dom_pre_inst                      false
% 1.43/0.99  --qbf_sk_in                             false
% 1.43/0.99  --qbf_pred_elim                         true
% 1.43/0.99  --qbf_split                             512
% 1.43/0.99  
% 1.43/0.99  ------ BMC1 Options
% 1.43/0.99  
% 1.43/0.99  --bmc1_incremental                      false
% 1.43/0.99  --bmc1_axioms                           reachable_all
% 1.43/0.99  --bmc1_min_bound                        0
% 1.43/0.99  --bmc1_max_bound                        -1
% 1.43/0.99  --bmc1_max_bound_default                -1
% 1.43/0.99  --bmc1_symbol_reachability              true
% 1.43/0.99  --bmc1_property_lemmas                  false
% 1.43/0.99  --bmc1_k_induction                      false
% 1.43/0.99  --bmc1_non_equiv_states                 false
% 1.43/0.99  --bmc1_deadlock                         false
% 1.43/0.99  --bmc1_ucm                              false
% 1.43/0.99  --bmc1_add_unsat_core                   none
% 1.43/0.99  --bmc1_unsat_core_children              false
% 1.43/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.99  --bmc1_out_stat                         full
% 1.43/0.99  --bmc1_ground_init                      false
% 1.43/0.99  --bmc1_pre_inst_next_state              false
% 1.43/0.99  --bmc1_pre_inst_state                   false
% 1.43/0.99  --bmc1_pre_inst_reach_state             false
% 1.43/0.99  --bmc1_out_unsat_core                   false
% 1.43/0.99  --bmc1_aig_witness_out                  false
% 1.43/0.99  --bmc1_verbose                          false
% 1.43/0.99  --bmc1_dump_clauses_tptp                false
% 1.43/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.99  --bmc1_dump_file                        -
% 1.43/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.99  --bmc1_ucm_extend_mode                  1
% 1.43/0.99  --bmc1_ucm_init_mode                    2
% 1.43/0.99  --bmc1_ucm_cone_mode                    none
% 1.43/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.99  --bmc1_ucm_relax_model                  4
% 1.43/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.99  --bmc1_ucm_layered_model                none
% 1.43/0.99  --bmc1_ucm_max_lemma_size               10
% 1.43/0.99  
% 1.43/0.99  ------ AIG Options
% 1.43/0.99  
% 1.43/0.99  --aig_mode                              false
% 1.43/0.99  
% 1.43/0.99  ------ Instantiation Options
% 1.43/0.99  
% 1.43/0.99  --instantiation_flag                    true
% 1.43/0.99  --inst_sos_flag                         false
% 1.43/0.99  --inst_sos_phase                        true
% 1.43/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.99  --inst_lit_sel_side                     num_symb
% 1.43/0.99  --inst_solver_per_active                1400
% 1.43/0.99  --inst_solver_calls_frac                1.
% 1.43/0.99  --inst_passive_queue_type               priority_queues
% 1.43/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.99  --inst_passive_queues_freq              [25;2]
% 1.43/0.99  --inst_dismatching                      true
% 1.43/0.99  --inst_eager_unprocessed_to_passive     true
% 1.43/0.99  --inst_prop_sim_given                   true
% 1.43/0.99  --inst_prop_sim_new                     false
% 1.43/0.99  --inst_subs_new                         false
% 1.43/0.99  --inst_eq_res_simp                      false
% 1.43/0.99  --inst_subs_given                       false
% 1.43/0.99  --inst_orphan_elimination               true
% 1.43/0.99  --inst_learning_loop_flag               true
% 1.43/0.99  --inst_learning_start                   3000
% 1.43/0.99  --inst_learning_factor                  2
% 1.43/0.99  --inst_start_prop_sim_after_learn       3
% 1.43/0.99  --inst_sel_renew                        solver
% 1.43/0.99  --inst_lit_activity_flag                true
% 1.43/0.99  --inst_restr_to_given                   false
% 1.43/0.99  --inst_activity_threshold               500
% 1.43/0.99  --inst_out_proof                        true
% 1.43/0.99  
% 1.43/0.99  ------ Resolution Options
% 1.43/0.99  
% 1.43/0.99  --resolution_flag                       true
% 1.43/0.99  --res_lit_sel                           adaptive
% 1.43/0.99  --res_lit_sel_side                      none
% 1.43/0.99  --res_ordering                          kbo
% 1.43/0.99  --res_to_prop_solver                    active
% 1.43/0.99  --res_prop_simpl_new                    false
% 1.43/0.99  --res_prop_simpl_given                  true
% 1.43/0.99  --res_passive_queue_type                priority_queues
% 1.43/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.99  --res_passive_queues_freq               [15;5]
% 1.43/0.99  --res_forward_subs                      full
% 1.43/0.99  --res_backward_subs                     full
% 1.43/0.99  --res_forward_subs_resolution           true
% 1.43/0.99  --res_backward_subs_resolution          true
% 1.43/0.99  --res_orphan_elimination                true
% 1.43/0.99  --res_time_limit                        2.
% 1.43/0.99  --res_out_proof                         true
% 1.43/0.99  
% 1.43/0.99  ------ Superposition Options
% 1.43/0.99  
% 1.43/0.99  --superposition_flag                    true
% 1.43/0.99  --sup_passive_queue_type                priority_queues
% 1.43/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.99  --demod_completeness_check              fast
% 1.43/0.99  --demod_use_ground                      true
% 1.43/0.99  --sup_to_prop_solver                    passive
% 1.43/0.99  --sup_prop_simpl_new                    true
% 1.43/0.99  --sup_prop_simpl_given                  true
% 1.43/0.99  --sup_fun_splitting                     false
% 1.43/0.99  --sup_smt_interval                      50000
% 1.43/0.99  
% 1.43/0.99  ------ Superposition Simplification Setup
% 1.43/0.99  
% 1.43/0.99  --sup_indices_passive                   []
% 1.43/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_full_bw                           [BwDemod]
% 1.43/0.99  --sup_immed_triv                        [TrivRules]
% 1.43/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_immed_bw_main                     []
% 1.43/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.99  
% 1.43/0.99  ------ Combination Options
% 1.43/0.99  
% 1.43/0.99  --comb_res_mult                         3
% 1.43/0.99  --comb_sup_mult                         2
% 1.43/0.99  --comb_inst_mult                        10
% 1.43/0.99  
% 1.43/0.99  ------ Debug Options
% 1.43/0.99  
% 1.43/0.99  --dbg_backtrace                         false
% 1.43/0.99  --dbg_dump_prop_clauses                 false
% 1.43/0.99  --dbg_dump_prop_clauses_file            -
% 1.43/0.99  --dbg_out_stat                          false
% 1.43/0.99  ------ Parsing...
% 1.43/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.43/0.99  ------ Proving...
% 1.43/0.99  ------ Problem Properties 
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  clauses                                 21
% 1.43/0.99  conjectures                             3
% 1.43/0.99  EPR                                     8
% 1.43/0.99  Horn                                    16
% 1.43/0.99  unary                                   4
% 1.43/0.99  binary                                  4
% 1.43/0.99  lits                                    68
% 1.43/0.99  lits eq                                 11
% 1.43/0.99  fd_pure                                 0
% 1.43/0.99  fd_pseudo                               0
% 1.43/0.99  fd_cond                                 4
% 1.43/0.99  fd_pseudo_cond                          3
% 1.43/0.99  AC symbols                              0
% 1.43/0.99  
% 1.43/0.99  ------ Schedule dynamic 5 is on 
% 1.43/0.99  
% 1.43/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  ------ 
% 1.43/0.99  Current options:
% 1.43/0.99  ------ 
% 1.43/0.99  
% 1.43/0.99  ------ Input Options
% 1.43/0.99  
% 1.43/0.99  --out_options                           all
% 1.43/0.99  --tptp_safe_out                         true
% 1.43/0.99  --problem_path                          ""
% 1.43/0.99  --include_path                          ""
% 1.43/0.99  --clausifier                            res/vclausify_rel
% 1.43/0.99  --clausifier_options                    --mode clausify
% 1.43/0.99  --stdin                                 false
% 1.43/0.99  --stats_out                             all
% 1.43/0.99  
% 1.43/0.99  ------ General Options
% 1.43/0.99  
% 1.43/0.99  --fof                                   false
% 1.43/0.99  --time_out_real                         305.
% 1.43/0.99  --time_out_virtual                      -1.
% 1.43/0.99  --symbol_type_check                     false
% 1.43/0.99  --clausify_out                          false
% 1.43/0.99  --sig_cnt_out                           false
% 1.43/0.99  --trig_cnt_out                          false
% 1.43/0.99  --trig_cnt_out_tolerance                1.
% 1.43/0.99  --trig_cnt_out_sk_spl                   false
% 1.43/0.99  --abstr_cl_out                          false
% 1.43/0.99  
% 1.43/0.99  ------ Global Options
% 1.43/0.99  
% 1.43/0.99  --schedule                              default
% 1.43/0.99  --add_important_lit                     false
% 1.43/0.99  --prop_solver_per_cl                    1000
% 1.43/0.99  --min_unsat_core                        false
% 1.43/0.99  --soft_assumptions                      false
% 1.43/0.99  --soft_lemma_size                       3
% 1.43/0.99  --prop_impl_unit_size                   0
% 1.43/0.99  --prop_impl_unit                        []
% 1.43/0.99  --share_sel_clauses                     true
% 1.43/0.99  --reset_solvers                         false
% 1.43/0.99  --bc_imp_inh                            [conj_cone]
% 1.43/0.99  --conj_cone_tolerance                   3.
% 1.43/0.99  --extra_neg_conj                        none
% 1.43/0.99  --large_theory_mode                     true
% 1.43/0.99  --prolific_symb_bound                   200
% 1.43/0.99  --lt_threshold                          2000
% 1.43/0.99  --clause_weak_htbl                      true
% 1.43/0.99  --gc_record_bc_elim                     false
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing Options
% 1.43/0.99  
% 1.43/0.99  --preprocessing_flag                    true
% 1.43/0.99  --time_out_prep_mult                    0.1
% 1.43/0.99  --splitting_mode                        input
% 1.43/0.99  --splitting_grd                         true
% 1.43/0.99  --splitting_cvd                         false
% 1.43/0.99  --splitting_cvd_svl                     false
% 1.43/0.99  --splitting_nvd                         32
% 1.43/0.99  --sub_typing                            true
% 1.43/0.99  --prep_gs_sim                           true
% 1.43/0.99  --prep_unflatten                        true
% 1.43/0.99  --prep_res_sim                          true
% 1.43/0.99  --prep_upred                            true
% 1.43/0.99  --prep_sem_filter                       exhaustive
% 1.43/0.99  --prep_sem_filter_out                   false
% 1.43/0.99  --pred_elim                             true
% 1.43/0.99  --res_sim_input                         true
% 1.43/0.99  --eq_ax_congr_red                       true
% 1.43/0.99  --pure_diseq_elim                       true
% 1.43/0.99  --brand_transform                       false
% 1.43/0.99  --non_eq_to_eq                          false
% 1.43/0.99  --prep_def_merge                        true
% 1.43/0.99  --prep_def_merge_prop_impl              false
% 1.43/0.99  --prep_def_merge_mbd                    true
% 1.43/0.99  --prep_def_merge_tr_red                 false
% 1.43/0.99  --prep_def_merge_tr_cl                  false
% 1.43/0.99  --smt_preprocessing                     true
% 1.43/0.99  --smt_ac_axioms                         fast
% 1.43/0.99  --preprocessed_out                      false
% 1.43/0.99  --preprocessed_stats                    false
% 1.43/0.99  
% 1.43/0.99  ------ Abstraction refinement Options
% 1.43/0.99  
% 1.43/0.99  --abstr_ref                             []
% 1.43/0.99  --abstr_ref_prep                        false
% 1.43/0.99  --abstr_ref_until_sat                   false
% 1.43/0.99  --abstr_ref_sig_restrict                funpre
% 1.43/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.99  --abstr_ref_under                       []
% 1.43/0.99  
% 1.43/0.99  ------ SAT Options
% 1.43/0.99  
% 1.43/0.99  --sat_mode                              false
% 1.43/0.99  --sat_fm_restart_options                ""
% 1.43/0.99  --sat_gr_def                            false
% 1.43/0.99  --sat_epr_types                         true
% 1.43/0.99  --sat_non_cyclic_types                  false
% 1.43/0.99  --sat_finite_models                     false
% 1.43/0.99  --sat_fm_lemmas                         false
% 1.43/0.99  --sat_fm_prep                           false
% 1.43/0.99  --sat_fm_uc_incr                        true
% 1.43/0.99  --sat_out_model                         small
% 1.43/0.99  --sat_out_clauses                       false
% 1.43/0.99  
% 1.43/0.99  ------ QBF Options
% 1.43/0.99  
% 1.43/0.99  --qbf_mode                              false
% 1.43/0.99  --qbf_elim_univ                         false
% 1.43/0.99  --qbf_dom_inst                          none
% 1.43/0.99  --qbf_dom_pre_inst                      false
% 1.43/0.99  --qbf_sk_in                             false
% 1.43/0.99  --qbf_pred_elim                         true
% 1.43/0.99  --qbf_split                             512
% 1.43/0.99  
% 1.43/0.99  ------ BMC1 Options
% 1.43/0.99  
% 1.43/0.99  --bmc1_incremental                      false
% 1.43/0.99  --bmc1_axioms                           reachable_all
% 1.43/0.99  --bmc1_min_bound                        0
% 1.43/0.99  --bmc1_max_bound                        -1
% 1.43/0.99  --bmc1_max_bound_default                -1
% 1.43/0.99  --bmc1_symbol_reachability              true
% 1.43/0.99  --bmc1_property_lemmas                  false
% 1.43/0.99  --bmc1_k_induction                      false
% 1.43/0.99  --bmc1_non_equiv_states                 false
% 1.43/0.99  --bmc1_deadlock                         false
% 1.43/0.99  --bmc1_ucm                              false
% 1.43/0.99  --bmc1_add_unsat_core                   none
% 1.43/0.99  --bmc1_unsat_core_children              false
% 1.43/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.99  --bmc1_out_stat                         full
% 1.43/0.99  --bmc1_ground_init                      false
% 1.43/0.99  --bmc1_pre_inst_next_state              false
% 1.43/0.99  --bmc1_pre_inst_state                   false
% 1.43/0.99  --bmc1_pre_inst_reach_state             false
% 1.43/0.99  --bmc1_out_unsat_core                   false
% 1.43/0.99  --bmc1_aig_witness_out                  false
% 1.43/0.99  --bmc1_verbose                          false
% 1.43/0.99  --bmc1_dump_clauses_tptp                false
% 1.43/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.99  --bmc1_dump_file                        -
% 1.43/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.99  --bmc1_ucm_extend_mode                  1
% 1.43/0.99  --bmc1_ucm_init_mode                    2
% 1.43/0.99  --bmc1_ucm_cone_mode                    none
% 1.43/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.99  --bmc1_ucm_relax_model                  4
% 1.43/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.99  --bmc1_ucm_layered_model                none
% 1.43/0.99  --bmc1_ucm_max_lemma_size               10
% 1.43/0.99  
% 1.43/0.99  ------ AIG Options
% 1.43/0.99  
% 1.43/0.99  --aig_mode                              false
% 1.43/0.99  
% 1.43/0.99  ------ Instantiation Options
% 1.43/0.99  
% 1.43/0.99  --instantiation_flag                    true
% 1.43/0.99  --inst_sos_flag                         false
% 1.43/0.99  --inst_sos_phase                        true
% 1.43/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.99  --inst_lit_sel_side                     none
% 1.43/0.99  --inst_solver_per_active                1400
% 1.43/0.99  --inst_solver_calls_frac                1.
% 1.43/0.99  --inst_passive_queue_type               priority_queues
% 1.43/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.99  --inst_passive_queues_freq              [25;2]
% 1.43/0.99  --inst_dismatching                      true
% 1.43/0.99  --inst_eager_unprocessed_to_passive     true
% 1.43/0.99  --inst_prop_sim_given                   true
% 1.43/0.99  --inst_prop_sim_new                     false
% 1.43/0.99  --inst_subs_new                         false
% 1.43/0.99  --inst_eq_res_simp                      false
% 1.43/0.99  --inst_subs_given                       false
% 1.43/0.99  --inst_orphan_elimination               true
% 1.43/0.99  --inst_learning_loop_flag               true
% 1.43/0.99  --inst_learning_start                   3000
% 1.43/0.99  --inst_learning_factor                  2
% 1.43/0.99  --inst_start_prop_sim_after_learn       3
% 1.43/0.99  --inst_sel_renew                        solver
% 1.43/0.99  --inst_lit_activity_flag                true
% 1.43/0.99  --inst_restr_to_given                   false
% 1.43/0.99  --inst_activity_threshold               500
% 1.43/0.99  --inst_out_proof                        true
% 1.43/0.99  
% 1.43/0.99  ------ Resolution Options
% 1.43/0.99  
% 1.43/0.99  --resolution_flag                       false
% 1.43/0.99  --res_lit_sel                           adaptive
% 1.43/0.99  --res_lit_sel_side                      none
% 1.43/0.99  --res_ordering                          kbo
% 1.43/0.99  --res_to_prop_solver                    active
% 1.43/0.99  --res_prop_simpl_new                    false
% 1.43/0.99  --res_prop_simpl_given                  true
% 1.43/0.99  --res_passive_queue_type                priority_queues
% 1.43/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.99  --res_passive_queues_freq               [15;5]
% 1.43/0.99  --res_forward_subs                      full
% 1.43/0.99  --res_backward_subs                     full
% 1.43/0.99  --res_forward_subs_resolution           true
% 1.43/0.99  --res_backward_subs_resolution          true
% 1.43/0.99  --res_orphan_elimination                true
% 1.43/0.99  --res_time_limit                        2.
% 1.43/0.99  --res_out_proof                         true
% 1.43/0.99  
% 1.43/0.99  ------ Superposition Options
% 1.43/0.99  
% 1.43/0.99  --superposition_flag                    true
% 1.43/0.99  --sup_passive_queue_type                priority_queues
% 1.43/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.99  --demod_completeness_check              fast
% 1.43/0.99  --demod_use_ground                      true
% 1.43/0.99  --sup_to_prop_solver                    passive
% 1.43/0.99  --sup_prop_simpl_new                    true
% 1.43/0.99  --sup_prop_simpl_given                  true
% 1.43/0.99  --sup_fun_splitting                     false
% 1.43/0.99  --sup_smt_interval                      50000
% 1.43/0.99  
% 1.43/0.99  ------ Superposition Simplification Setup
% 1.43/0.99  
% 1.43/0.99  --sup_indices_passive                   []
% 1.43/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_full_bw                           [BwDemod]
% 1.43/0.99  --sup_immed_triv                        [TrivRules]
% 1.43/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_immed_bw_main                     []
% 1.43/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.99  
% 1.43/0.99  ------ Combination Options
% 1.43/0.99  
% 1.43/0.99  --comb_res_mult                         3
% 1.43/0.99  --comb_sup_mult                         2
% 1.43/0.99  --comb_inst_mult                        10
% 1.43/0.99  
% 1.43/0.99  ------ Debug Options
% 1.43/0.99  
% 1.43/0.99  --dbg_backtrace                         false
% 1.43/0.99  --dbg_dump_prop_clauses                 false
% 1.43/0.99  --dbg_dump_prop_clauses_file            -
% 1.43/0.99  --dbg_out_stat                          false
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  ------ Proving...
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  % SZS status Theorem for theBenchmark.p
% 1.43/0.99  
% 1.43/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.43/0.99  
% 1.43/0.99  fof(f5,axiom,(
% 1.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f15,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f5])).
% 1.43/0.99  
% 1.43/0.99  fof(f16,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f15])).
% 1.43/0.99  
% 1.43/0.99  fof(f50,plain,(
% 1.43/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f16])).
% 1.43/0.99  
% 1.43/0.99  fof(f8,conjecture,(
% 1.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f9,negated_conjecture,(
% 1.43/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.43/0.99    inference(negated_conjecture,[],[f8])).
% 1.43/0.99  
% 1.43/0.99  fof(f21,plain,(
% 1.43/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f9])).
% 1.43/0.99  
% 1.43/0.99  fof(f22,plain,(
% 1.43/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f21])).
% 1.43/0.99  
% 1.43/0.99  fof(f31,plain,(
% 1.43/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.43/0.99    inference(nnf_transformation,[],[f22])).
% 1.43/0.99  
% 1.43/0.99  fof(f32,plain,(
% 1.43/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f31])).
% 1.43/0.99  
% 1.43/0.99  fof(f36,plain,(
% 1.43/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.43/0.99    introduced(choice_axiom,[])).
% 1.43/0.99  
% 1.43/0.99  fof(f35,plain,(
% 1.43/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.43/0.99    introduced(choice_axiom,[])).
% 1.43/0.99  
% 1.43/0.99  fof(f34,plain,(
% 1.43/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.43/0.99    introduced(choice_axiom,[])).
% 1.43/0.99  
% 1.43/0.99  fof(f33,plain,(
% 1.43/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.43/0.99    introduced(choice_axiom,[])).
% 1.43/0.99  
% 1.43/0.99  fof(f37,plain,(
% 1.43/0.99    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f36,f35,f34,f33])).
% 1.43/0.99  
% 1.43/0.99  fof(f59,plain,(
% 1.43/0.99    l1_orders_2(sK1)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f55,plain,(
% 1.43/0.99    ~v2_struct_0(sK1)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f56,plain,(
% 1.43/0.99    v3_orders_2(sK1)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f57,plain,(
% 1.43/0.99    v4_orders_2(sK1)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f58,plain,(
% 1.43/0.99    v5_orders_2(sK1)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f1,axiom,(
% 1.43/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f23,plain,(
% 1.43/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.43/0.99    inference(nnf_transformation,[],[f1])).
% 1.43/0.99  
% 1.43/0.99  fof(f24,plain,(
% 1.43/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.43/0.99    inference(flattening,[],[f23])).
% 1.43/0.99  
% 1.43/0.99  fof(f38,plain,(
% 1.43/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f24])).
% 1.43/0.99  
% 1.43/0.99  fof(f63,plain,(
% 1.43/0.99    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f60,plain,(
% 1.43/0.99    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f62,plain,(
% 1.43/0.99    m2_orders_2(sK4,sK1,sK2)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f4,axiom,(
% 1.43/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f13,plain,(
% 1.43/0.99    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f4])).
% 1.43/0.99  
% 1.43/0.99  fof(f14,plain,(
% 1.43/0.99    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f13])).
% 1.43/0.99  
% 1.43/0.99  fof(f49,plain,(
% 1.43/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f14])).
% 1.43/0.99  
% 1.43/0.99  fof(f7,axiom,(
% 1.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f19,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f7])).
% 1.43/0.99  
% 1.43/0.99  fof(f20,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f19])).
% 1.43/0.99  
% 1.43/0.99  fof(f30,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(nnf_transformation,[],[f20])).
% 1.43/0.99  
% 1.43/0.99  fof(f54,plain,(
% 1.43/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f30])).
% 1.43/0.99  
% 1.43/0.99  fof(f6,axiom,(
% 1.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f17,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f6])).
% 1.43/0.99  
% 1.43/0.99  fof(f18,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f17])).
% 1.43/0.99  
% 1.43/0.99  fof(f51,plain,(
% 1.43/0.99    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f18])).
% 1.43/0.99  
% 1.43/0.99  fof(f48,plain,(
% 1.43/0.99    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f14])).
% 1.43/0.99  
% 1.43/0.99  fof(f3,axiom,(
% 1.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f11,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.99    inference(ennf_transformation,[],[f3])).
% 1.43/0.99  
% 1.43/0.99  fof(f12,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f11])).
% 1.43/0.99  
% 1.43/0.99  fof(f25,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(nnf_transformation,[],[f12])).
% 1.43/0.99  
% 1.43/0.99  fof(f26,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(flattening,[],[f25])).
% 1.43/0.99  
% 1.43/0.99  fof(f27,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(rectify,[],[f26])).
% 1.43/0.99  
% 1.43/0.99  fof(f28,plain,(
% 1.43/0.99    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.43/0.99    introduced(choice_axiom,[])).
% 1.43/0.99  
% 1.43/0.99  fof(f29,plain,(
% 1.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.43/0.99  
% 1.43/0.99  fof(f42,plain,(
% 1.43/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f29])).
% 1.43/0.99  
% 1.43/0.99  fof(f66,plain,(
% 1.43/0.99    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.99    inference(equality_resolution,[],[f42])).
% 1.43/0.99  
% 1.43/0.99  fof(f39,plain,(
% 1.43/0.99    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f24])).
% 1.43/0.99  
% 1.43/0.99  fof(f65,plain,(
% 1.43/0.99    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.43/0.99    inference(equality_resolution,[],[f39])).
% 1.43/0.99  
% 1.43/0.99  fof(f40,plain,(
% 1.43/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f24])).
% 1.43/0.99  
% 1.43/0.99  fof(f64,plain,(
% 1.43/0.99    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  fof(f2,axiom,(
% 1.43/0.99    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.43/0.99  
% 1.43/0.99  fof(f10,plain,(
% 1.43/0.99    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.43/0.99    inference(ennf_transformation,[],[f2])).
% 1.43/0.99  
% 1.43/0.99  fof(f41,plain,(
% 1.43/0.99    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.99    inference(cnf_transformation,[],[f10])).
% 1.43/0.99  
% 1.43/0.99  fof(f61,plain,(
% 1.43/0.99    m2_orders_2(sK3,sK1,sK2)),
% 1.43/0.99    inference(cnf_transformation,[],[f37])).
% 1.43/0.99  
% 1.43/0.99  cnf(c_12,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | r1_tarski(X0,X2)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_22,negated_conjecture,
% 1.43/0.99      ( l1_orders_2(sK1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_965,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | r1_tarski(X0,X2)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | sK1 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_966,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(X0,X1)
% 1.43/0.99      | v2_struct_0(sK1)
% 1.43/0.99      | ~ v3_orders_2(sK1)
% 1.43/0.99      | ~ v4_orders_2(sK1)
% 1.43/0.99      | ~ v5_orders_2(sK1) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_965]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_26,negated_conjecture,
% 1.43/0.99      ( ~ v2_struct_0(sK1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_25,negated_conjecture,
% 1.43/0.99      ( v3_orders_2(sK1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_24,negated_conjecture,
% 1.43/0.99      ( v4_orders_2(sK1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_23,negated_conjecture,
% 1.43/0.99      ( v5_orders_2(sK1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_970,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(X0,X1) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_966,c_26,c_25,c_24,c_23]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1745,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0_55,sK1,X1_55)
% 1.43/0.99      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(X0_55,X1_55) ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_970]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2397,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0_55,sK1,sK3)
% 1.43/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(X0_55,sK3) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1745]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2716,plain,
% 1.43/0.99      ( ~ m1_orders_2(sK4,sK1,sK3)
% 1.43/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(sK4,sK3) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2397]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1777,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0_55,X0_56,X1_55)
% 1.43/0.99      | m1_orders_2(X2_55,X0_56,X3_55)
% 1.43/0.99      | X2_55 != X0_55
% 1.43/0.99      | X3_55 != X1_55 ),
% 1.43/0.99      theory(equality) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2371,plain,
% 1.43/0.99      ( m1_orders_2(X0_55,sK1,X1_55)
% 1.43/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | X1_55 != sK4
% 1.43/0.99      | X0_55 != sK3 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1777]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2477,plain,
% 1.43/0.99      ( m1_orders_2(X0_55,sK1,sK4)
% 1.43/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | X0_55 != sK3
% 1.43/0.99      | sK4 != sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2371]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2704,plain,
% 1.43/0.99      ( m1_orders_2(sK4,sK1,sK4)
% 1.43/0.99      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | sK4 != sK4
% 1.43/0.99      | sK4 != sK3 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2477]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2,plain,
% 1.43/0.99      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_18,negated_conjecture,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.43/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_210,plain,
% 1.43/0.99      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 1.43/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_211,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_410,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | r1_tarski(X0,X1)
% 1.43/0.99      | sK4 != X1
% 1.43/0.99      | sK3 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_211]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_411,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1757,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_411]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2161,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.43/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_21,negated_conjecture,
% 1.43/0.99      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 1.43/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_32,plain,
% 1.43/0.99      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_19,negated_conjecture,
% 1.43/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.43/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_34,plain,
% 1.43/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_412,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.43/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_10,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_986,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | sK1 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_987,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,sK1,X1)
% 1.43/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | v2_struct_0(sK1)
% 1.43/0.99      | ~ v3_orders_2(sK1)
% 1.43/0.99      | ~ v4_orders_2(sK1)
% 1.43/0.99      | ~ v5_orders_2(sK1) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_986]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_989,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,sK1,X1)
% 1.43/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_987,c_26,c_25,c_24,c_23]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1744,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0_55,sK1,X0_57)
% 1.43/0.99      | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_989]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2351,plain,
% 1.43/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.43/0.99      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1744]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2352,plain,
% 1.43/0.99      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.43/0.99      | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_2351]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2387,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0_55,sK1,sK4)
% 1.43/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(X0_55,sK4) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1745]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2512,plain,
% 1.43/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | r1_tarski(sK3,sK4) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2513,plain,
% 1.43/0.99      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.43/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.99      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_2512]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2647,plain,
% 1.43/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_2161,c_32,c_34,c_412,c_2352,c_2513]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2649,plain,
% 1.43/0.99      ( r1_tarski(sK3,sK4) ),
% 1.43/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2647]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_15,plain,
% 1.43/0.99      ( m1_orders_2(X0,X1,X2)
% 1.43/0.99      | m1_orders_2(X2,X1,X0)
% 1.43/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.43/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.43/0.99      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X1)
% 1.43/0.99      | X0 = X2 ),
% 1.43/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_918,plain,
% 1.43/0.99      ( m1_orders_2(X0,X1,X2)
% 1.43/0.99      | m1_orders_2(X2,X1,X0)
% 1.43/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.43/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.43/0.99      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | X2 = X0
% 1.43/0.99      | sK1 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_919,plain,
% 1.43/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.43/0.99      | m1_orders_2(X1,sK1,X0)
% 1.43/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.43/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | v2_struct_0(sK1)
% 1.43/0.99      | ~ v3_orders_2(sK1)
% 1.43/0.99      | ~ v4_orders_2(sK1)
% 1.43/0.99      | ~ v5_orders_2(sK1)
% 1.43/0.99      | X0 = X1 ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_918]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_921,plain,
% 1.43/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.43/0.99      | m1_orders_2(X1,sK1,X0)
% 1.43/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.43/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | X0 = X1 ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_919,c_26,c_25,c_24,c_23]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_922,plain,
% 1.43/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.43/0.99      | m1_orders_2(X1,sK1,X0)
% 1.43/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.43/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | X0 = X1 ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_921]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1747,plain,
% 1.43/0.99      ( m1_orders_2(X0_55,sK1,X1_55)
% 1.43/0.99      | m1_orders_2(X1_55,sK1,X0_55)
% 1.43/0.99      | ~ m2_orders_2(X0_55,sK1,X0_57)
% 1.43/0.99      | ~ m2_orders_2(X1_55,sK1,X0_57)
% 1.43/0.99      | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | X0_55 = X1_55 ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_922]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2423,plain,
% 1.43/0.99      ( m1_orders_2(X0_55,sK1,sK4)
% 1.43/0.99      | m1_orders_2(sK4,sK1,X0_55)
% 1.43/0.99      | ~ m2_orders_2(X0_55,sK1,X0_57)
% 1.43/0.99      | ~ m2_orders_2(sK4,sK1,X0_57)
% 1.43/0.99      | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | X0_55 = sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1747]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2633,plain,
% 1.43/0.99      ( m1_orders_2(sK4,sK1,sK3)
% 1.43/0.99      | m1_orders_2(sK3,sK1,sK4)
% 1.43/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.43/0.99      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.43/0.99      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | sK3 = sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2423]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1766,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2478,plain,
% 1.43/0.99      ( sK4 = sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1766]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_14,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X1)
% 1.43/0.99      | k1_xboole_0 = X0 ),
% 1.43/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_944,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | sK1 != X1
% 1.43/0.99      | k1_xboole_0 = X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_945,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | v2_struct_0(sK1)
% 1.43/0.99      | ~ v3_orders_2(sK1)
% 1.43/0.99      | ~ v4_orders_2(sK1)
% 1.43/0.99      | ~ v5_orders_2(sK1)
% 1.43/0.99      | k1_xboole_0 = X0 ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_944]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_949,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0,sK1,X0)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | k1_xboole_0 = X0 ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_945,c_26,c_25,c_24,c_23]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1746,plain,
% 1.43/0.99      ( ~ m1_orders_2(X0_55,sK1,X0_55)
% 1.43/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | k1_xboole_0 = X0_55 ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_949]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2411,plain,
% 1.43/0.99      ( ~ m1_orders_2(sK4,sK1,sK4)
% 1.43/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.99      | k1_xboole_0 = sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1746]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1771,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0_55,X0_56,X0_57)
% 1.43/0.99      | m2_orders_2(X1_55,X0_56,X0_57)
% 1.43/0.99      | X1_55 != X0_55 ),
% 1.43/0.99      theory(equality) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2361,plain,
% 1.43/0.99      ( m2_orders_2(X0_55,sK1,sK2)
% 1.43/0.99      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.43/0.99      | X0_55 != sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1771]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2363,plain,
% 1.43/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.43/0.99      | m2_orders_2(k1_xboole_0,sK1,sK2)
% 1.43/0.99      | k1_xboole_0 != sK4 ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2361]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2354,plain,
% 1.43/0.99      ( ~ m2_orders_2(sK3,sK1,sK2)
% 1.43/0.99      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1744]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_11,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | v6_orders_2(X0,X1)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X1) ),
% 1.43/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_9,plain,
% 1.43/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.43/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ v6_orders_2(k1_xboole_0,X0)
% 1.43/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ v3_orders_2(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | ~ v5_orders_2(X0)
% 1.43/0.99      | ~ l1_orders_2(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_644,plain,
% 1.43/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.43/0.99      | ~ m2_orders_2(k1_xboole_0,X3,X4)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
% 1.43/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v2_struct_0(X3)
% 1.43/0.99      | ~ v3_orders_2(X1)
% 1.43/0.99      | ~ v3_orders_2(X3)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | ~ v4_orders_2(X3)
% 1.43/0.99      | ~ v5_orders_2(X1)
% 1.43/0.99      | ~ v5_orders_2(X3)
% 1.43/0.99      | ~ l1_orders_2(X1)
% 1.43/0.99      | ~ l1_orders_2(X3)
% 1.43/0.99      | X3 != X1
% 1.43/0.99      | k1_xboole_0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_9]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_645,plain,
% 1.43/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.43/0.99      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ v3_orders_2(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | ~ v5_orders_2(X0)
% 1.43/0.99      | ~ l1_orders_2(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_644]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_669,plain,
% 1.43/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.43/0.99      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.43/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ v3_orders_2(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | ~ v5_orders_2(X0)
% 1.43/0.99      | ~ l1_orders_2(X0) ),
% 1.43/0.99      inference(forward_subsumption_resolution,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_645,c_10]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_753,plain,
% 1.43/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.43/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.43/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.43/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.43/1.00      | v2_struct_0(X0)
% 1.43/1.00      | ~ v3_orders_2(X0)
% 1.43/1.00      | ~ v4_orders_2(X0)
% 1.43/1.00      | ~ v5_orders_2(X0)
% 1.43/1.00      | sK1 != X0 ),
% 1.43/1.00      inference(resolution_lifted,[status(thm)],[c_669,c_22]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_754,plain,
% 1.43/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.43/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.43/1.00      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | v2_struct_0(sK1)
% 1.43/1.00      | ~ v3_orders_2(sK1)
% 1.43/1.00      | ~ v4_orders_2(sK1)
% 1.43/1.00      | ~ v5_orders_2(sK1) ),
% 1.43/1.00      inference(unflattening,[status(thm)],[c_753]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_758,plain,
% 1.43/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.43/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.43/1.00      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) ),
% 1.43/1.00      inference(global_propositional_subsumption,
% 1.43/1.00                [status(thm)],
% 1.43/1.00                [c_754,c_26,c_25,c_24,c_23]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1754,plain,
% 1.43/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0_57)
% 1.43/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1_57)
% 1.43/1.00      | ~ m1_orders_1(X1_57,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1))) ),
% 1.43/1.00      inference(subtyping,[status(esa)],[c_758]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1763,plain,
% 1.43/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0_57)
% 1.43/1.00      | ~ m1_orders_1(X0_57,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | ~ sP0_iProver_split ),
% 1.43/1.00      inference(splitting,
% 1.43/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.43/1.00                [c_1754]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1800,plain,
% 1.43/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,sK2)
% 1.43/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.43/1.00      | ~ sP0_iProver_split ),
% 1.43/1.00      inference(instantiation,[status(thm)],[c_1763]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1764,plain,
% 1.43/1.00      ( sP0_iProver_split ),
% 1.43/1.00      inference(splitting,
% 1.43/1.00                [splitting(split),new_symbols(definition,[])],
% 1.43/1.00                [c_1754]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1,plain,
% 1.43/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 1.43/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_420,plain,
% 1.43/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 1.43/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_211]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_421,plain,
% 1.43/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.43/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1756,plain,
% 1.43/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.43/1.00      inference(subtyping,[status(esa)],[c_421]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_0,plain,
% 1.43/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.43/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_17,negated_conjecture,
% 1.43/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.43/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_208,plain,
% 1.43/1.00      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 1.43/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_209,plain,
% 1.43/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.43/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_397,plain,
% 1.43/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.43/1.00      | ~ r1_tarski(X0,X1)
% 1.43/1.00      | X1 = X0
% 1.43/1.00      | sK4 != X1
% 1.43/1.00      | sK3 != X0 ),
% 1.43/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_209]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_398,plain,
% 1.43/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.43/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_1758,plain,
% 1.43/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.43/1.00      inference(subtyping,[status(esa)],[c_398]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_3,plain,
% 1.43/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 1.43/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_430,plain,
% 1.43/1.00      ( m1_orders_2(sK3,sK1,sK4)
% 1.43/1.00      | ~ r1_tarski(X0,X1)
% 1.43/1.00      | sK4 != X0
% 1.43/1.00      | sK3 != X1 ),
% 1.43/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_211]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_431,plain,
% 1.43/1.00      ( m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK4,sK3) ),
% 1.43/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(c_20,negated_conjecture,
% 1.43/1.00      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.43/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.43/1.00  
% 1.43/1.00  cnf(contradiction,plain,
% 1.43/1.00      ( $false ),
% 1.43/1.00      inference(minisat,
% 1.43/1.00                [status(thm)],
% 1.43/1.00                [c_2716,c_2704,c_2649,c_2633,c_2478,c_2411,c_2363,c_2354,
% 1.43/1.00                 c_2351,c_1800,c_1764,c_1756,c_1758,c_431,c_19,c_20,c_21]) ).
% 1.43/1.00  
% 1.43/1.00  
% 1.43/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.43/1.00  
% 1.43/1.00  ------                               Statistics
% 1.43/1.00  
% 1.43/1.00  ------ General
% 1.43/1.00  
% 1.43/1.00  abstr_ref_over_cycles:                  0
% 1.43/1.00  abstr_ref_under_cycles:                 0
% 1.43/1.00  gc_basic_clause_elim:                   0
% 1.43/1.00  forced_gc_time:                         0
% 1.43/1.00  parsing_time:                           0.01
% 1.43/1.00  unif_index_cands_time:                  0.
% 1.43/1.00  unif_index_add_time:                    0.
% 1.43/1.00  orderings_time:                         0.
% 1.43/1.00  out_proof_time:                         0.013
% 1.43/1.00  total_time:                             0.117
% 1.43/1.00  num_of_symbols:                         63
% 1.43/1.00  num_of_terms:                           1999
% 1.43/1.00  
% 1.43/1.00  ------ Preprocessing
% 1.43/1.00  
% 1.43/1.00  num_of_splits:                          2
% 1.43/1.00  num_of_split_atoms:                     1
% 1.43/1.00  num_of_reused_defs:                     1
% 1.43/1.00  num_eq_ax_congr_red:                    35
% 1.43/1.00  num_of_sem_filtered_clauses:            2
% 1.43/1.00  num_of_subtypes:                        7
% 1.43/1.00  monotx_restored_types:                  1
% 1.43/1.00  sat_num_of_epr_types:                   0
% 1.43/1.00  sat_num_of_non_cyclic_types:            0
% 1.43/1.00  sat_guarded_non_collapsed_types:        1
% 1.43/1.00  num_pure_diseq_elim:                    0
% 1.43/1.00  simp_replaced_by:                       0
% 1.43/1.00  res_preprocessed:                       110
% 1.43/1.00  prep_upred:                             0
% 1.43/1.00  prep_unflattend:                        44
% 1.43/1.00  smt_new_axioms:                         0
% 1.43/1.00  pred_elim_cands:                        6
% 1.43/1.00  pred_elim:                              8
% 1.43/1.00  pred_elim_cl:                           8
% 1.43/1.00  pred_elim_cycles:                       14
% 1.43/1.00  merged_defs:                            2
% 1.43/1.00  merged_defs_ncl:                        0
% 1.43/1.00  bin_hyper_res:                          2
% 1.43/1.00  prep_cycles:                            4
% 1.43/1.00  pred_elim_time:                         0.031
% 1.43/1.00  splitting_time:                         0.
% 1.43/1.00  sem_filter_time:                        0.
% 1.43/1.00  monotx_time:                            0.
% 1.43/1.00  subtype_inf_time:                       0.001
% 1.43/1.00  
% 1.43/1.00  ------ Problem properties
% 1.43/1.00  
% 1.43/1.00  clauses:                                21
% 1.43/1.00  conjectures:                            3
% 1.43/1.00  epr:                                    8
% 1.43/1.00  horn:                                   16
% 1.43/1.00  ground:                                 9
% 1.43/1.00  unary:                                  4
% 1.43/1.00  binary:                                 4
% 1.43/1.00  lits:                                   68
% 1.43/1.00  lits_eq:                                11
% 1.43/1.00  fd_pure:                                0
% 1.43/1.00  fd_pseudo:                              0
% 1.43/1.00  fd_cond:                                4
% 1.43/1.00  fd_pseudo_cond:                         3
% 1.43/1.00  ac_symbols:                             0
% 1.43/1.00  
% 1.43/1.00  ------ Propositional Solver
% 1.43/1.00  
% 1.43/1.00  prop_solver_calls:                      26
% 1.43/1.00  prop_fast_solver_calls:                 1262
% 1.43/1.00  smt_solver_calls:                       0
% 1.43/1.00  smt_fast_solver_calls:                  0
% 1.43/1.00  prop_num_of_clauses:                    445
% 1.43/1.00  prop_preprocess_simplified:             3179
% 1.43/1.00  prop_fo_subsumed:                       59
% 1.43/1.00  prop_solver_time:                       0.
% 1.43/1.00  smt_solver_time:                        0.
% 1.43/1.00  smt_fast_solver_time:                   0.
% 1.43/1.00  prop_fast_solver_time:                  0.
% 1.43/1.00  prop_unsat_core_time:                   0.
% 1.43/1.00  
% 1.43/1.00  ------ QBF
% 1.43/1.00  
% 1.43/1.00  qbf_q_res:                              0
% 1.43/1.00  qbf_num_tautologies:                    0
% 1.43/1.00  qbf_prep_cycles:                        0
% 1.43/1.00  
% 1.43/1.00  ------ BMC1
% 1.43/1.00  
% 1.43/1.00  bmc1_current_bound:                     -1
% 1.43/1.00  bmc1_last_solved_bound:                 -1
% 1.43/1.00  bmc1_unsat_core_size:                   -1
% 1.43/1.00  bmc1_unsat_core_parents_size:           -1
% 1.43/1.00  bmc1_merge_next_fun:                    0
% 1.43/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.43/1.00  
% 1.43/1.00  ------ Instantiation
% 1.43/1.00  
% 1.43/1.00  inst_num_of_clauses:                    93
% 1.43/1.00  inst_num_in_passive:                    11
% 1.43/1.00  inst_num_in_active:                     77
% 1.43/1.00  inst_num_in_unprocessed:                4
% 1.43/1.00  inst_num_of_loops:                      82
% 1.43/1.00  inst_num_of_learning_restarts:          0
% 1.43/1.00  inst_num_moves_active_passive:          1
% 1.43/1.00  inst_lit_activity:                      0
% 1.43/1.00  inst_lit_activity_moves:                0
% 1.43/1.00  inst_num_tautologies:                   0
% 1.43/1.00  inst_num_prop_implied:                  0
% 1.43/1.00  inst_num_existing_simplified:           0
% 1.43/1.00  inst_num_eq_res_simplified:             0
% 1.43/1.00  inst_num_child_elim:                    0
% 1.43/1.00  inst_num_of_dismatching_blockings:      4
% 1.43/1.00  inst_num_of_non_proper_insts:           90
% 1.43/1.00  inst_num_of_duplicates:                 0
% 1.43/1.00  inst_inst_num_from_inst_to_res:         0
% 1.43/1.00  inst_dismatching_checking_time:         0.
% 1.43/1.00  
% 1.43/1.00  ------ Resolution
% 1.43/1.00  
% 1.43/1.00  res_num_of_clauses:                     0
% 1.43/1.00  res_num_in_passive:                     0
% 1.43/1.00  res_num_in_active:                      0
% 1.43/1.00  res_num_of_loops:                       114
% 1.43/1.00  res_forward_subset_subsumed:            15
% 1.43/1.00  res_backward_subset_subsumed:           0
% 1.43/1.00  res_forward_subsumed:                   0
% 1.43/1.00  res_backward_subsumed:                  0
% 1.43/1.00  res_forward_subsumption_resolution:     3
% 1.43/1.00  res_backward_subsumption_resolution:    0
% 1.43/1.00  res_clause_to_clause_subsumption:       82
% 1.43/1.00  res_orphan_elimination:                 0
% 1.43/1.00  res_tautology_del:                      20
% 1.43/1.00  res_num_eq_res_simplified:              0
% 1.43/1.00  res_num_sel_changes:                    0
% 1.43/1.00  res_moves_from_active_to_pass:          0
% 1.43/1.00  
% 1.43/1.00  ------ Superposition
% 1.43/1.00  
% 1.43/1.00  sup_time_total:                         0.
% 1.43/1.00  sup_time_generating:                    0.
% 1.43/1.00  sup_time_sim_full:                      0.
% 1.43/1.00  sup_time_sim_immed:                     0.
% 1.43/1.00  
% 1.43/1.00  sup_num_of_clauses:                     26
% 1.43/1.00  sup_num_in_active:                      16
% 1.43/1.00  sup_num_in_passive:                     10
% 1.43/1.00  sup_num_of_loops:                       16
% 1.43/1.00  sup_fw_superposition:                   3
% 1.43/1.00  sup_bw_superposition:                   3
% 1.43/1.00  sup_immediate_simplified:               0
% 1.43/1.00  sup_given_eliminated:                   0
% 1.43/1.00  comparisons_done:                       0
% 1.43/1.00  comparisons_avoided:                    0
% 1.43/1.00  
% 1.43/1.00  ------ Simplifications
% 1.43/1.00  
% 1.43/1.00  
% 1.43/1.00  sim_fw_subset_subsumed:                 1
% 1.43/1.00  sim_bw_subset_subsumed:                 0
% 1.43/1.00  sim_fw_subsumed:                        0
% 1.43/1.00  sim_bw_subsumed:                        0
% 1.43/1.00  sim_fw_subsumption_res:                 1
% 1.43/1.00  sim_bw_subsumption_res:                 0
% 1.43/1.00  sim_tautology_del:                      0
% 1.43/1.00  sim_eq_tautology_del:                   0
% 1.43/1.00  sim_eq_res_simp:                        0
% 1.43/1.00  sim_fw_demodulated:                     0
% 1.43/1.00  sim_bw_demodulated:                     0
% 1.43/1.00  sim_light_normalised:                   0
% 1.43/1.00  sim_joinable_taut:                      0
% 1.43/1.00  sim_joinable_simp:                      0
% 1.43/1.00  sim_ac_normalised:                      0
% 1.43/1.00  sim_smt_subsumption:                    0
% 1.43/1.00  
%------------------------------------------------------------------------------
