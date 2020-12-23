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
% DateTime   : Thu Dec  3 12:12:47 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  162 (1634 expanded)
%              Number of clauses        :  102 ( 309 expanded)
%              Number of leaves         :   15 ( 529 expanded)
%              Depth                    :   20
%              Number of atoms          :  902 (15725 expanded)
%              Number of equality atoms :  180 ( 383 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f37,f36,f35,f34])).

fof(f67,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f66,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f10,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f45])).

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

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_216,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_217,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_394,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_217])).

cnf(c_395,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_2136,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_23,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_396,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_945,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_946,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_945])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_948,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_28,c_27,c_26,c_25])).

cnf(c_2324,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_2325,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_962,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_963,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_965,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_28,c_27,c_26,c_25])).

cnf(c_2315,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_2363,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2364,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2363])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_218,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_219,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_417,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_219])).

cnf(c_418,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_2134,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_22,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_407,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_219])).

cnf(c_408,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_409,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_419,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2366,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2367,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2461,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2739,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_2740,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2739])).

cnf(c_2138,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2139,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2137,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_898,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_899,plain,
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
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_901,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_28,c_27,c_26,c_25])).

cnf(c_902,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_2124,plain,
    ( X0 = X1
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m2_orders_2(X1,sK1,X2) != iProver_top
    | m2_orders_2(X0,sK1,X2) != iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_2522,plain,
    ( X0 = X1
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_2124])).

cnf(c_3004,plain,
    ( sK4 = X0
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_2522])).

cnf(c_3034,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_3004])).

cnf(c_2455,plain,
    ( m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | ~ m2_orders_2(X0,sK1,X1)
    | ~ m2_orders_2(sK4,sK1,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_2673,plain,
    ( m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2455])).

cnf(c_2768,plain,
    ( m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_2769,plain,
    ( sK3 = sK4
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

cnf(c_3085,plain,
    ( m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3034,c_34,c_35,c_36,c_419,c_2769])).

cnf(c_3157,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_3158,plain,
    ( m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3157])).

cnf(c_3249,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_34,c_35,c_409,c_419,c_2367,c_2740,c_3085,c_3158])).

cnf(c_3579,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2136,c_34,c_35,c_36,c_396,c_409,c_419,c_2325,c_2364,c_2367,c_2740,c_3085,c_3158])).

cnf(c_3582,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3579,c_3249])).

cnf(c_13,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_624,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_11])).

cnf(c_625,plain,
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
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_649,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_625,c_12])).

cnf(c_733,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_649,c_24])).

cnf(c_734,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_738,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_28,c_27,c_26,c_25])).

cnf(c_1719,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_738])).

cnf(c_2132,plain,
    ( m2_orders_2(k1_xboole_0,sK1,X0) != iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_1720,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_738])).

cnf(c_2131,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1720])).

cnf(c_2185,plain,
    ( m2_orders_2(k1_xboole_0,sK1,X0) != iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2132,c_2131])).

cnf(c_3491,plain,
    ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_2185])).

cnf(c_1722,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2890,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_1725,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2341,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | X2 != sK2
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2497,plain,
    ( m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | X1 != sK1
    | X0 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_2889,plain,
    ( m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | X0 != sK3
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_2891,plain,
    ( X0 != sK3
    | sK2 != sK2
    | sK1 != sK1
    | m2_orders_2(X0,sK1,sK2) = iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2889])).

cnf(c_2893,plain,
    ( sK2 != sK2
    | sK1 != sK1
    | k1_xboole_0 != sK3
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2891])).

cnf(c_16,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_924,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_925,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_929,plain,
    ( ~ m1_orders_2(X0,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_925,c_28,c_27,c_26,c_25])).

cnf(c_2839,plain,
    ( ~ m1_orders_2(sK3,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_2842,plain,
    ( k1_xboole_0 = sK3
    | m1_orders_2(sK3,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2839])).

cnf(c_2396,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3582,c_3491,c_2890,c_2893,c_2842,c_2396,c_2367,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.99  
% 1.99/0.99  ------  iProver source info
% 1.99/0.99  
% 1.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.99  git: non_committed_changes: false
% 1.99/0.99  git: last_make_outside_of_git: false
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     num_symb
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       true
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  ------ Parsing...
% 1.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.99  ------ Proving...
% 1.99/0.99  ------ Problem Properties 
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  clauses                                 21
% 1.99/0.99  conjectures                             3
% 1.99/0.99  EPR                                     8
% 1.99/0.99  Horn                                    16
% 1.99/0.99  unary                                   5
% 1.99/0.99  binary                                  3
% 1.99/0.99  lits                                    67
% 1.99/0.99  lits eq                                 11
% 1.99/0.99  fd_pure                                 0
% 1.99/0.99  fd_pseudo                               0
% 1.99/0.99  fd_cond                                 4
% 1.99/0.99  fd_pseudo_cond                          3
% 1.99/0.99  AC symbols                              0
% 1.99/0.99  
% 1.99/0.99  ------ Schedule dynamic 5 is on 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  Current options:
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/1.00  
% 1.99/1.00  ------ General Options
% 1.99/1.00  
% 1.99/1.00  --fof                                   false
% 1.99/1.00  --time_out_real                         305.
% 1.99/1.00  --time_out_virtual                      -1.
% 1.99/1.00  --symbol_type_check                     false
% 1.99/1.00  --clausify_out                          false
% 1.99/1.00  --sig_cnt_out                           false
% 1.99/1.00  --trig_cnt_out                          false
% 1.99/1.00  --trig_cnt_out_tolerance                1.
% 1.99/1.00  --trig_cnt_out_sk_spl                   false
% 1.99/1.00  --abstr_cl_out                          false
% 1.99/1.00  
% 1.99/1.00  ------ Global Options
% 1.99/1.00  
% 1.99/1.00  --schedule                              default
% 1.99/1.00  --add_important_lit                     false
% 1.99/1.00  --prop_solver_per_cl                    1000
% 1.99/1.00  --min_unsat_core                        false
% 1.99/1.00  --soft_assumptions                      false
% 1.99/1.00  --soft_lemma_size                       3
% 1.99/1.00  --prop_impl_unit_size                   0
% 1.99/1.00  --prop_impl_unit                        []
% 1.99/1.00  --share_sel_clauses                     true
% 1.99/1.00  --reset_solvers                         false
% 1.99/1.00  --bc_imp_inh                            [conj_cone]
% 1.99/1.00  --conj_cone_tolerance                   3.
% 1.99/1.00  --extra_neg_conj                        none
% 1.99/1.00  --large_theory_mode                     true
% 1.99/1.00  --prolific_symb_bound                   200
% 1.99/1.00  --lt_threshold                          2000
% 1.99/1.00  --clause_weak_htbl                      true
% 1.99/1.00  --gc_record_bc_elim                     false
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing Options
% 1.99/1.00  
% 1.99/1.00  --preprocessing_flag                    true
% 1.99/1.00  --time_out_prep_mult                    0.1
% 1.99/1.00  --splitting_mode                        input
% 1.99/1.00  --splitting_grd                         true
% 1.99/1.00  --splitting_cvd                         false
% 1.99/1.00  --splitting_cvd_svl                     false
% 1.99/1.00  --splitting_nvd                         32
% 1.99/1.00  --sub_typing                            true
% 1.99/1.00  --prep_gs_sim                           true
% 1.99/1.00  --prep_unflatten                        true
% 1.99/1.00  --prep_res_sim                          true
% 1.99/1.00  --prep_upred                            true
% 1.99/1.00  --prep_sem_filter                       exhaustive
% 1.99/1.00  --prep_sem_filter_out                   false
% 1.99/1.00  --pred_elim                             true
% 1.99/1.00  --res_sim_input                         true
% 1.99/1.00  --eq_ax_congr_red                       true
% 1.99/1.00  --pure_diseq_elim                       true
% 1.99/1.00  --brand_transform                       false
% 1.99/1.00  --non_eq_to_eq                          false
% 1.99/1.00  --prep_def_merge                        true
% 1.99/1.00  --prep_def_merge_prop_impl              false
% 1.99/1.00  --prep_def_merge_mbd                    true
% 1.99/1.00  --prep_def_merge_tr_red                 false
% 1.99/1.00  --prep_def_merge_tr_cl                  false
% 1.99/1.00  --smt_preprocessing                     true
% 1.99/1.00  --smt_ac_axioms                         fast
% 1.99/1.00  --preprocessed_out                      false
% 1.99/1.00  --preprocessed_stats                    false
% 1.99/1.00  
% 1.99/1.00  ------ Abstraction refinement Options
% 1.99/1.00  
% 1.99/1.00  --abstr_ref                             []
% 1.99/1.00  --abstr_ref_prep                        false
% 1.99/1.00  --abstr_ref_until_sat                   false
% 1.99/1.00  --abstr_ref_sig_restrict                funpre
% 1.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.00  --abstr_ref_under                       []
% 1.99/1.00  
% 1.99/1.00  ------ SAT Options
% 1.99/1.00  
% 1.99/1.00  --sat_mode                              false
% 1.99/1.00  --sat_fm_restart_options                ""
% 1.99/1.00  --sat_gr_def                            false
% 1.99/1.00  --sat_epr_types                         true
% 1.99/1.00  --sat_non_cyclic_types                  false
% 1.99/1.00  --sat_finite_models                     false
% 1.99/1.00  --sat_fm_lemmas                         false
% 1.99/1.00  --sat_fm_prep                           false
% 1.99/1.00  --sat_fm_uc_incr                        true
% 1.99/1.00  --sat_out_model                         small
% 1.99/1.00  --sat_out_clauses                       false
% 1.99/1.00  
% 1.99/1.00  ------ QBF Options
% 1.99/1.00  
% 1.99/1.00  --qbf_mode                              false
% 1.99/1.00  --qbf_elim_univ                         false
% 1.99/1.00  --qbf_dom_inst                          none
% 1.99/1.00  --qbf_dom_pre_inst                      false
% 1.99/1.00  --qbf_sk_in                             false
% 1.99/1.00  --qbf_pred_elim                         true
% 1.99/1.00  --qbf_split                             512
% 1.99/1.00  
% 1.99/1.00  ------ BMC1 Options
% 1.99/1.00  
% 1.99/1.00  --bmc1_incremental                      false
% 1.99/1.00  --bmc1_axioms                           reachable_all
% 1.99/1.00  --bmc1_min_bound                        0
% 1.99/1.00  --bmc1_max_bound                        -1
% 1.99/1.00  --bmc1_max_bound_default                -1
% 1.99/1.00  --bmc1_symbol_reachability              true
% 1.99/1.00  --bmc1_property_lemmas                  false
% 1.99/1.00  --bmc1_k_induction                      false
% 1.99/1.00  --bmc1_non_equiv_states                 false
% 1.99/1.00  --bmc1_deadlock                         false
% 1.99/1.00  --bmc1_ucm                              false
% 1.99/1.00  --bmc1_add_unsat_core                   none
% 1.99/1.00  --bmc1_unsat_core_children              false
% 1.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.00  --bmc1_out_stat                         full
% 1.99/1.00  --bmc1_ground_init                      false
% 1.99/1.00  --bmc1_pre_inst_next_state              false
% 1.99/1.00  --bmc1_pre_inst_state                   false
% 1.99/1.00  --bmc1_pre_inst_reach_state             false
% 1.99/1.00  --bmc1_out_unsat_core                   false
% 1.99/1.00  --bmc1_aig_witness_out                  false
% 1.99/1.00  --bmc1_verbose                          false
% 1.99/1.00  --bmc1_dump_clauses_tptp                false
% 1.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.00  --bmc1_dump_file                        -
% 1.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.00  --bmc1_ucm_extend_mode                  1
% 1.99/1.00  --bmc1_ucm_init_mode                    2
% 1.99/1.00  --bmc1_ucm_cone_mode                    none
% 1.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.00  --bmc1_ucm_relax_model                  4
% 1.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.00  --bmc1_ucm_layered_model                none
% 1.99/1.00  --bmc1_ucm_max_lemma_size               10
% 1.99/1.00  
% 1.99/1.00  ------ AIG Options
% 1.99/1.00  
% 1.99/1.00  --aig_mode                              false
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation Options
% 1.99/1.00  
% 1.99/1.00  --instantiation_flag                    true
% 1.99/1.00  --inst_sos_flag                         false
% 1.99/1.00  --inst_sos_phase                        true
% 1.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel_side                     none
% 1.99/1.00  --inst_solver_per_active                1400
% 1.99/1.00  --inst_solver_calls_frac                1.
% 1.99/1.00  --inst_passive_queue_type               priority_queues
% 1.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.00  --inst_passive_queues_freq              [25;2]
% 1.99/1.00  --inst_dismatching                      true
% 1.99/1.00  --inst_eager_unprocessed_to_passive     true
% 1.99/1.00  --inst_prop_sim_given                   true
% 1.99/1.00  --inst_prop_sim_new                     false
% 1.99/1.00  --inst_subs_new                         false
% 1.99/1.00  --inst_eq_res_simp                      false
% 1.99/1.00  --inst_subs_given                       false
% 1.99/1.00  --inst_orphan_elimination               true
% 1.99/1.00  --inst_learning_loop_flag               true
% 1.99/1.00  --inst_learning_start                   3000
% 1.99/1.00  --inst_learning_factor                  2
% 1.99/1.00  --inst_start_prop_sim_after_learn       3
% 1.99/1.00  --inst_sel_renew                        solver
% 1.99/1.00  --inst_lit_activity_flag                true
% 1.99/1.00  --inst_restr_to_given                   false
% 1.99/1.00  --inst_activity_threshold               500
% 1.99/1.00  --inst_out_proof                        true
% 1.99/1.00  
% 1.99/1.00  ------ Resolution Options
% 1.99/1.00  
% 1.99/1.00  --resolution_flag                       false
% 1.99/1.00  --res_lit_sel                           adaptive
% 1.99/1.00  --res_lit_sel_side                      none
% 1.99/1.00  --res_ordering                          kbo
% 1.99/1.00  --res_to_prop_solver                    active
% 1.99/1.00  --res_prop_simpl_new                    false
% 1.99/1.00  --res_prop_simpl_given                  true
% 1.99/1.00  --res_passive_queue_type                priority_queues
% 1.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.00  --res_passive_queues_freq               [15;5]
% 1.99/1.00  --res_forward_subs                      full
% 1.99/1.00  --res_backward_subs                     full
% 1.99/1.00  --res_forward_subs_resolution           true
% 1.99/1.00  --res_backward_subs_resolution          true
% 1.99/1.00  --res_orphan_elimination                true
% 1.99/1.00  --res_time_limit                        2.
% 1.99/1.00  --res_out_proof                         true
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Options
% 1.99/1.00  
% 1.99/1.00  --superposition_flag                    true
% 1.99/1.00  --sup_passive_queue_type                priority_queues
% 1.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.00  --demod_completeness_check              fast
% 1.99/1.00  --demod_use_ground                      true
% 1.99/1.00  --sup_to_prop_solver                    passive
% 1.99/1.00  --sup_prop_simpl_new                    true
% 1.99/1.00  --sup_prop_simpl_given                  true
% 1.99/1.00  --sup_fun_splitting                     false
% 1.99/1.00  --sup_smt_interval                      50000
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Simplification Setup
% 1.99/1.00  
% 1.99/1.00  --sup_indices_passive                   []
% 1.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_full_bw                           [BwDemod]
% 1.99/1.00  --sup_immed_triv                        [TrivRules]
% 1.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_immed_bw_main                     []
% 1.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  
% 1.99/1.00  ------ Combination Options
% 1.99/1.00  
% 1.99/1.00  --comb_res_mult                         3
% 1.99/1.00  --comb_sup_mult                         2
% 1.99/1.00  --comb_inst_mult                        10
% 1.99/1.00  
% 1.99/1.00  ------ Debug Options
% 1.99/1.00  
% 1.99/1.00  --dbg_backtrace                         false
% 1.99/1.00  --dbg_dump_prop_clauses                 false
% 1.99/1.00  --dbg_dump_prop_clauses_file            -
% 1.99/1.00  --dbg_out_stat                          false
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  ------ Proving...
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS status Theorem for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  fof(f1,axiom,(
% 1.99/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f22,plain,(
% 1.99/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.99/1.00    inference(nnf_transformation,[],[f1])).
% 1.99/1.00  
% 1.99/1.00  fof(f23,plain,(
% 1.99/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.99/1.00    inference(flattening,[],[f22])).
% 1.99/1.00  
% 1.99/1.00  fof(f41,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f23])).
% 1.99/1.00  
% 1.99/1.00  fof(f8,conjecture,(
% 1.99/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f9,negated_conjecture,(
% 1.99/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.99/1.00    inference(negated_conjecture,[],[f8])).
% 1.99/1.00  
% 1.99/1.00  fof(f20,plain,(
% 1.99/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f9])).
% 1.99/1.00  
% 1.99/1.00  fof(f21,plain,(
% 1.99/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f20])).
% 1.99/1.00  
% 1.99/1.00  fof(f32,plain,(
% 1.99/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.99/1.00    inference(nnf_transformation,[],[f21])).
% 1.99/1.00  
% 1.99/1.00  fof(f33,plain,(
% 1.99/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f32])).
% 1.99/1.00  
% 1.99/1.00  fof(f37,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f36,plain,(
% 1.99/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f35,plain,(
% 1.99/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f34,plain,(
% 1.99/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f38,plain,(
% 1.99/1.00    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f37,f36,f35,f34])).
% 1.99/1.00  
% 1.99/1.00  fof(f67,plain,(
% 1.99/1.00    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f63,plain,(
% 1.99/1.00    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f65,plain,(
% 1.99/1.00    m2_orders_2(sK4,sK1,sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f5,axiom,(
% 1.99/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f14,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f5])).
% 1.99/1.00  
% 1.99/1.00  fof(f15,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f14])).
% 1.99/1.00  
% 1.99/1.00  fof(f53,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f15])).
% 1.99/1.00  
% 1.99/1.00  fof(f62,plain,(
% 1.99/1.00    l1_orders_2(sK1)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f58,plain,(
% 1.99/1.00    ~v2_struct_0(sK1)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f59,plain,(
% 1.99/1.00    v3_orders_2(sK1)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f60,plain,(
% 1.99/1.00    v4_orders_2(sK1)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f61,plain,(
% 1.99/1.00    v5_orders_2(sK1)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f4,axiom,(
% 1.99/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f12,plain,(
% 1.99/1.00    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f4])).
% 1.99/1.00  
% 1.99/1.00  fof(f13,plain,(
% 1.99/1.00    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f12])).
% 1.99/1.00  
% 1.99/1.00  fof(f52,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f13])).
% 1.99/1.00  
% 1.99/1.00  fof(f40,plain,(
% 1.99/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f23])).
% 1.99/1.00  
% 1.99/1.00  fof(f68,plain,(
% 1.99/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.99/1.00    inference(equality_resolution,[],[f40])).
% 1.99/1.00  
% 1.99/1.00  fof(f66,plain,(
% 1.99/1.00    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f64,plain,(
% 1.99/1.00    m2_orders_2(sK3,sK1,sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f39,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f23])).
% 1.99/1.00  
% 1.99/1.00  fof(f2,axiom,(
% 1.99/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f24,plain,(
% 1.99/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/1.00    inference(nnf_transformation,[],[f2])).
% 1.99/1.00  
% 1.99/1.00  fof(f25,plain,(
% 1.99/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/1.00    inference(flattening,[],[f24])).
% 1.99/1.00  
% 1.99/1.00  fof(f44,plain,(
% 1.99/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f25])).
% 1.99/1.00  
% 1.99/1.00  fof(f7,axiom,(
% 1.99/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f18,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f7])).
% 1.99/1.00  
% 1.99/1.00  fof(f19,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f18])).
% 1.99/1.00  
% 1.99/1.00  fof(f31,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(nnf_transformation,[],[f19])).
% 1.99/1.00  
% 1.99/1.00  fof(f57,plain,(
% 1.99/1.00    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f31])).
% 1.99/1.00  
% 1.99/1.00  fof(f51,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f13])).
% 1.99/1.00  
% 1.99/1.00  fof(f3,axiom,(
% 1.99/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f10,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f3])).
% 1.99/1.00  
% 1.99/1.00  fof(f11,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f10])).
% 1.99/1.00  
% 1.99/1.00  fof(f26,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(nnf_transformation,[],[f11])).
% 1.99/1.00  
% 1.99/1.00  fof(f27,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f26])).
% 1.99/1.00  
% 1.99/1.00  fof(f28,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(rectify,[],[f27])).
% 1.99/1.00  
% 1.99/1.00  fof(f29,plain,(
% 1.99/1.00    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f30,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 1.99/1.00  
% 1.99/1.00  fof(f45,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f30])).
% 1.99/1.00  
% 1.99/1.00  fof(f71,plain,(
% 1.99/1.00    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(equality_resolution,[],[f45])).
% 1.99/1.00  
% 1.99/1.00  fof(f6,axiom,(
% 1.99/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f16,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f6])).
% 1.99/1.00  
% 1.99/1.00  fof(f17,plain,(
% 1.99/1.00    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/1.00    inference(flattening,[],[f16])).
% 1.99/1.00  
% 1.99/1.00  fof(f54,plain,(
% 1.99/1.00    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f17])).
% 1.99/1.00  
% 1.99/1.00  cnf(c_0,plain,
% 1.99/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_19,negated_conjecture,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.99/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_216,plain,
% 1.99/1.00      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 1.99/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_217,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.99/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_394,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.99/1.00      | ~ r1_tarski(X0,X1)
% 1.99/1.00      | X1 = X0
% 1.99/1.00      | sK4 != X1
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_217]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_395,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2136,plain,
% 1.99/1.00      ( sK4 = sK3
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.99/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_23,negated_conjecture,
% 1.99/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_34,plain,
% 1.99/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_21,negated_conjecture,
% 1.99/1.00      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_36,plain,
% 1.99/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_396,plain,
% 1.99/1.00      ( sK4 = sK3
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.99/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_14,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | r1_tarski(X0,X2)
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_24,negated_conjecture,
% 1.99/1.00      ( l1_orders_2(sK1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_945,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | r1_tarski(X0,X2)
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | sK1 != X1 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_946,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.99/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | r1_tarski(X0,X1)
% 1.99/1.00      | v2_struct_0(sK1)
% 1.99/1.00      | ~ v3_orders_2(sK1)
% 1.99/1.00      | ~ v4_orders_2(sK1)
% 1.99/1.00      | ~ v5_orders_2(sK1) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_945]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_28,negated_conjecture,
% 1.99/1.00      ( ~ v2_struct_0(sK1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_27,negated_conjecture,
% 1.99/1.00      ( v3_orders_2(sK1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_26,negated_conjecture,
% 1.99/1.00      ( v4_orders_2(sK1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_25,negated_conjecture,
% 1.99/1.00      ( v5_orders_2(sK1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_948,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.99/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | r1_tarski(X0,X1) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_946,c_28,c_27,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2324,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | r1_tarski(sK3,sK4) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_948]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2325,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_12,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_962,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | sK1 != X1 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_963,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,sK1,X1)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | v2_struct_0(sK1)
% 1.99/1.00      | ~ v3_orders_2(sK1)
% 1.99/1.00      | ~ v4_orders_2(sK1)
% 1.99/1.00      | ~ v5_orders_2(sK1) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_962]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_965,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,sK1,X1)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_963,c_28,c_27,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2315,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.99/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_965]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2363,plain,
% 1.99/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.99/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2364,plain,
% 1.99/1.00      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.99/1.00      | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 1.99/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2363]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1,plain,
% 1.99/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_20,negated_conjecture,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.99/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_218,plain,
% 1.99/1.00      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 1.99/1.00      inference(prop_impl,[status(thm)],[c_20]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_219,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.99/1.00      inference(renaming,[status(thm)],[c_218]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_417,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_219]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_418,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2134,plain,
% 1.99/1.00      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_22,negated_conjecture,
% 1.99/1.00      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_35,plain,
% 1.99/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2,plain,
% 1.99/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_407,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4)
% 1.99/1.00      | r1_tarski(X0,X1)
% 1.99/1.00      | sK4 != X1
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_219]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_408,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_409,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.99/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_419,plain,
% 1.99/1.00      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2366,plain,
% 1.99/1.00      ( ~ m2_orders_2(sK3,sK1,sK2)
% 1.99/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2367,plain,
% 1.99/1.00      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.99/1.00      | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 1.99/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3,plain,
% 1.99/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2461,plain,
% 1.99/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2739,plain,
% 1.99/1.00      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2461]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2740,plain,
% 1.99/1.00      ( sK3 = sK4
% 1.99/1.00      | r1_tarski(sK4,sK3) != iProver_top
% 1.99/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2739]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2138,plain,
% 1.99/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2139,plain,
% 1.99/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2137,plain,
% 1.99/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_17,plain,
% 1.99/1.00      ( m1_orders_2(X0,X1,X2)
% 1.99/1.00      | m1_orders_2(X2,X1,X0)
% 1.99/1.00      | ~ m2_orders_2(X2,X1,X3)
% 1.99/1.00      | ~ m2_orders_2(X0,X1,X3)
% 1.99/1.00      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X1)
% 1.99/1.00      | X0 = X2 ),
% 1.99/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_898,plain,
% 1.99/1.00      ( m1_orders_2(X0,X1,X2)
% 1.99/1.00      | m1_orders_2(X2,X1,X0)
% 1.99/1.00      | ~ m2_orders_2(X2,X1,X3)
% 1.99/1.00      | ~ m2_orders_2(X0,X1,X3)
% 1.99/1.00      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | X2 = X0
% 1.99/1.00      | sK1 != X1 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_899,plain,
% 1.99/1.00      ( m1_orders_2(X0,sK1,X1)
% 1.99/1.00      | m1_orders_2(X1,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(X1,sK1,X2)
% 1.99/1.00      | ~ m2_orders_2(X0,sK1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | v2_struct_0(sK1)
% 1.99/1.00      | ~ v3_orders_2(sK1)
% 1.99/1.00      | ~ v4_orders_2(sK1)
% 1.99/1.00      | ~ v5_orders_2(sK1)
% 1.99/1.00      | X0 = X1 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_898]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_901,plain,
% 1.99/1.00      ( m1_orders_2(X0,sK1,X1)
% 1.99/1.00      | m1_orders_2(X1,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(X1,sK1,X2)
% 1.99/1.00      | ~ m2_orders_2(X0,sK1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | X0 = X1 ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_899,c_28,c_27,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_902,plain,
% 1.99/1.00      ( m1_orders_2(X0,sK1,X1)
% 1.99/1.00      | m1_orders_2(X1,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(X0,sK1,X2)
% 1.99/1.00      | ~ m2_orders_2(X1,sK1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | X0 = X1 ),
% 1.99/1.00      inference(renaming,[status(thm)],[c_901]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2124,plain,
% 1.99/1.00      ( X0 = X1
% 1.99/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top
% 1.99/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top
% 1.99/1.00      | m2_orders_2(X1,sK1,X2) != iProver_top
% 1.99/1.00      | m2_orders_2(X0,sK1,X2) != iProver_top
% 1.99/1.00      | m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2522,plain,
% 1.99/1.00      ( X0 = X1
% 1.99/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top
% 1.99/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top
% 1.99/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 1.99/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2137,c_2124]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3004,plain,
% 1.99/1.00      ( sK4 = X0
% 1.99/1.00      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 1.99/1.00      | m1_orders_2(sK4,sK1,X0) = iProver_top
% 1.99/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2139,c_2522]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3034,plain,
% 1.99/1.00      ( sK4 = sK3
% 1.99/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2138,c_3004]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2455,plain,
% 1.99/1.00      ( m1_orders_2(X0,sK1,sK4)
% 1.99/1.00      | m1_orders_2(sK4,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(X0,sK1,X1)
% 1.99/1.00      | ~ m2_orders_2(sK4,sK1,X1)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | X0 = sK4 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_902]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2673,plain,
% 1.99/1.00      ( m1_orders_2(X0,sK1,sK4)
% 1.99/1.00      | m1_orders_2(sK4,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(X0,sK1,sK2)
% 1.99/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.99/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | X0 = sK4 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2455]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2768,plain,
% 1.99/1.00      ( m1_orders_2(sK4,sK1,sK3)
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4)
% 1.99/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.99/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.99/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | sK3 = sK4 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2673]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2769,plain,
% 1.99/1.00      ( sK3 = sK4
% 1.99/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.99/1.00      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.99/1.00      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.99/1.00      | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3085,plain,
% 1.99/1.00      ( m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_3034,c_34,c_35,c_36,c_419,c_2769]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3157,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK4,sK1,sK3)
% 1.99/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | r1_tarski(sK4,sK3) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_948]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3158,plain,
% 1.99/1.00      ( m1_orders_2(sK4,sK1,sK3) != iProver_top
% 1.99/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/1.00      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_3157]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3249,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_2134,c_34,c_35,c_409,c_419,c_2367,c_2740,c_3085,
% 1.99/1.00                 c_3158]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3579,plain,
% 1.99/1.00      ( sK4 = sK3 ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_2136,c_34,c_35,c_36,c_396,c_409,c_419,c_2325,c_2364,
% 1.99/1.00                 c_2367,c_2740,c_3085,c_3158]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3582,plain,
% 1.99/1.00      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 1.99/1.00      inference(demodulation,[status(thm)],[c_3579,c_3249]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_13,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | v6_orders_2(X0,X1)
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_11,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | ~ v6_orders_2(k1_xboole_0,X0)
% 1.99/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/1.00      | v2_struct_0(X0)
% 1.99/1.00      | ~ v3_orders_2(X0)
% 1.99/1.00      | ~ v4_orders_2(X0)
% 1.99/1.00      | ~ v5_orders_2(X0)
% 1.99/1.00      | ~ l1_orders_2(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_624,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,X3,X4)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.99/1.00      | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
% 1.99/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | v2_struct_0(X3)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v3_orders_2(X3)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X3)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X3)
% 1.99/1.00      | ~ l1_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X3)
% 1.99/1.00      | X3 != X1
% 1.99/1.00      | k1_xboole_0 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_11]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_625,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/1.00      | v2_struct_0(X0)
% 1.99/1.00      | ~ v3_orders_2(X0)
% 1.99/1.00      | ~ v4_orders_2(X0)
% 1.99/1.00      | ~ v5_orders_2(X0)
% 1.99/1.00      | ~ l1_orders_2(X0) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_624]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_649,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | v2_struct_0(X0)
% 1.99/1.00      | ~ v3_orders_2(X0)
% 1.99/1.00      | ~ v4_orders_2(X0)
% 1.99/1.00      | ~ v5_orders_2(X0)
% 1.99/1.00      | ~ l1_orders_2(X0) ),
% 1.99/1.00      inference(forward_subsumption_resolution,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_625,c_12]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_733,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.99/1.00      | v2_struct_0(X0)
% 1.99/1.00      | ~ v3_orders_2(X0)
% 1.99/1.00      | ~ v4_orders_2(X0)
% 1.99/1.00      | ~ v5_orders_2(X0)
% 1.99/1.00      | sK1 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_649,c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_734,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.99/1.00      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | v2_struct_0(sK1)
% 1.99/1.00      | ~ v3_orders_2(sK1)
% 1.99/1.00      | ~ v4_orders_2(sK1)
% 1.99/1.00      | ~ v5_orders_2(sK1) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_733]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_738,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.99/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.99/1.00      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_734,c_28,c_27,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1719,plain,
% 1.99/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.99/1.00      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1)))
% 1.99/1.00      | ~ sP0_iProver_split ),
% 1.99/1.00      inference(splitting,
% 1.99/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.99/1.00                [c_738]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2132,plain,
% 1.99/1.00      ( m2_orders_2(k1_xboole_0,sK1,X0) != iProver_top
% 1.99/1.00      | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 1.99/1.00      | sP0_iProver_split != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1719]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1720,plain,
% 1.99/1.00      ( sP0_iProver_split ),
% 1.99/1.00      inference(splitting,
% 1.99/1.00                [splitting(split),new_symbols(definition,[])],
% 1.99/1.00                [c_738]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2131,plain,
% 1.99/1.00      ( sP0_iProver_split = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1720]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2185,plain,
% 1.99/1.00      ( m2_orders_2(k1_xboole_0,sK1,X0) != iProver_top
% 1.99/1.00      | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK1))) != iProver_top ),
% 1.99/1.00      inference(forward_subsumption_resolution,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_2132,c_2131]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_3491,plain,
% 1.99/1.00      ( m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2137,c_2185]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1722,plain,( X0 = X0 ),theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2890,plain,
% 1.99/1.00      ( sK1 = sK1 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1722]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1725,plain,
% 1.99/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/1.00      | m2_orders_2(X3,X4,X5)
% 1.99/1.00      | X3 != X0
% 1.99/1.00      | X4 != X1
% 1.99/1.00      | X5 != X2 ),
% 1.99/1.00      theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2341,plain,
% 1.99/1.00      ( m2_orders_2(X0,X1,X2)
% 1.99/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.99/1.00      | X2 != sK2
% 1.99/1.00      | X1 != sK1
% 1.99/1.00      | X0 != sK3 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1725]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2497,plain,
% 1.99/1.00      ( m2_orders_2(X0,X1,sK2)
% 1.99/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.99/1.00      | X1 != sK1
% 1.99/1.00      | X0 != sK3
% 1.99/1.00      | sK2 != sK2 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2341]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2889,plain,
% 1.99/1.00      ( m2_orders_2(X0,sK1,sK2)
% 1.99/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.99/1.00      | X0 != sK3
% 1.99/1.00      | sK2 != sK2
% 1.99/1.00      | sK1 != sK1 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2891,plain,
% 1.99/1.00      ( X0 != sK3
% 1.99/1.00      | sK2 != sK2
% 1.99/1.00      | sK1 != sK1
% 1.99/1.00      | m2_orders_2(X0,sK1,sK2) = iProver_top
% 1.99/1.00      | m2_orders_2(sK3,sK1,sK2) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2889]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2893,plain,
% 1.99/1.00      ( sK2 != sK2
% 1.99/1.00      | sK1 != sK1
% 1.99/1.00      | k1_xboole_0 != sK3
% 1.99/1.00      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.99/1.00      | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_2891]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_16,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,X1,X0)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | ~ l1_orders_2(X1)
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_924,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,X1,X0)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.00      | v2_struct_0(X1)
% 1.99/1.00      | ~ v3_orders_2(X1)
% 1.99/1.00      | ~ v4_orders_2(X1)
% 1.99/1.00      | ~ v5_orders_2(X1)
% 1.99/1.00      | sK1 != X1
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_925,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,sK1,X0)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | v2_struct_0(sK1)
% 1.99/1.00      | ~ v3_orders_2(sK1)
% 1.99/1.00      | ~ v4_orders_2(sK1)
% 1.99/1.00      | ~ v5_orders_2(sK1)
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_924]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_929,plain,
% 1.99/1.00      ( ~ m1_orders_2(X0,sK1,X0)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_925,c_28,c_27,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2839,plain,
% 1.99/1.00      ( ~ m1_orders_2(sK3,sK1,sK3)
% 1.99/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/1.00      | k1_xboole_0 = sK3 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2842,plain,
% 1.99/1.00      ( k1_xboole_0 = sK3
% 1.99/1.00      | m1_orders_2(sK3,sK1,sK3) != iProver_top
% 1.99/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2839]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2396,plain,
% 1.99/1.00      ( sK2 = sK2 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1722]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(contradiction,plain,
% 1.99/1.00      ( $false ),
% 1.99/1.00      inference(minisat,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_3582,c_3491,c_2890,c_2893,c_2842,c_2396,c_2367,c_35,
% 1.99/1.00                 c_34]) ).
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  ------                               Statistics
% 1.99/1.00  
% 1.99/1.00  ------ General
% 1.99/1.00  
% 1.99/1.00  abstr_ref_over_cycles:                  0
% 1.99/1.00  abstr_ref_under_cycles:                 0
% 1.99/1.00  gc_basic_clause_elim:                   0
% 1.99/1.00  forced_gc_time:                         0
% 1.99/1.00  parsing_time:                           0.009
% 1.99/1.00  unif_index_cands_time:                  0.
% 1.99/1.00  unif_index_add_time:                    0.
% 1.99/1.00  orderings_time:                         0.
% 1.99/1.00  out_proof_time:                         0.009
% 1.99/1.00  total_time:                             0.161
% 1.99/1.00  num_of_symbols:                         59
% 1.99/1.00  num_of_terms:                           2400
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing
% 1.99/1.00  
% 1.99/1.00  num_of_splits:                          2
% 1.99/1.00  num_of_split_atoms:                     1
% 1.99/1.00  num_of_reused_defs:                     1
% 1.99/1.00  num_eq_ax_congr_red:                    23
% 1.99/1.00  num_of_sem_filtered_clauses:            2
% 1.99/1.00  num_of_subtypes:                        0
% 1.99/1.00  monotx_restored_types:                  0
% 1.99/1.00  sat_num_of_epr_types:                   0
% 1.99/1.00  sat_num_of_non_cyclic_types:            0
% 1.99/1.00  sat_guarded_non_collapsed_types:        0
% 1.99/1.00  num_pure_diseq_elim:                    0
% 1.99/1.00  simp_replaced_by:                       0
% 1.99/1.00  res_preprocessed:                       117
% 1.99/1.00  prep_upred:                             0
% 1.99/1.00  prep_unflattend:                        40
% 1.99/1.00  smt_new_axioms:                         0
% 1.99/1.00  pred_elim_cands:                        6
% 1.99/1.00  pred_elim:                              8
% 1.99/1.00  pred_elim_cl:                           9
% 1.99/1.00  pred_elim_cycles:                       14
% 1.99/1.00  merged_defs:                            2
% 1.99/1.00  merged_defs_ncl:                        0
% 1.99/1.00  bin_hyper_res:                          2
% 1.99/1.00  prep_cycles:                            4
% 1.99/1.00  pred_elim_time:                         0.039
% 1.99/1.00  splitting_time:                         0.
% 1.99/1.00  sem_filter_time:                        0.
% 1.99/1.00  monotx_time:                            0.001
% 1.99/1.00  subtype_inf_time:                       0.
% 1.99/1.00  
% 1.99/1.00  ------ Problem properties
% 1.99/1.00  
% 1.99/1.00  clauses:                                21
% 1.99/1.00  conjectures:                            3
% 1.99/1.00  epr:                                    8
% 1.99/1.00  horn:                                   16
% 1.99/1.00  ground:                                 8
% 1.99/1.00  unary:                                  5
% 1.99/1.00  binary:                                 3
% 1.99/1.00  lits:                                   67
% 1.99/1.00  lits_eq:                                11
% 1.99/1.00  fd_pure:                                0
% 1.99/1.00  fd_pseudo:                              0
% 1.99/1.00  fd_cond:                                4
% 1.99/1.00  fd_pseudo_cond:                         3
% 1.99/1.00  ac_symbols:                             0
% 1.99/1.00  
% 1.99/1.00  ------ Propositional Solver
% 1.99/1.00  
% 1.99/1.00  prop_solver_calls:                      28
% 1.99/1.00  prop_fast_solver_calls:                 1392
% 1.99/1.00  smt_solver_calls:                       0
% 1.99/1.00  smt_fast_solver_calls:                  0
% 1.99/1.00  prop_num_of_clauses:                    767
% 1.99/1.00  prop_preprocess_simplified:             4076
% 1.99/1.00  prop_fo_subsumed:                       60
% 1.99/1.00  prop_solver_time:                       0.
% 1.99/1.00  smt_solver_time:                        0.
% 1.99/1.00  smt_fast_solver_time:                   0.
% 1.99/1.00  prop_fast_solver_time:                  0.
% 1.99/1.00  prop_unsat_core_time:                   0.
% 1.99/1.00  
% 1.99/1.00  ------ QBF
% 1.99/1.00  
% 1.99/1.00  qbf_q_res:                              0
% 1.99/1.00  qbf_num_tautologies:                    0
% 1.99/1.00  qbf_prep_cycles:                        0
% 1.99/1.00  
% 1.99/1.00  ------ BMC1
% 1.99/1.00  
% 1.99/1.00  bmc1_current_bound:                     -1
% 1.99/1.00  bmc1_last_solved_bound:                 -1
% 1.99/1.00  bmc1_unsat_core_size:                   -1
% 1.99/1.00  bmc1_unsat_core_parents_size:           -1
% 1.99/1.00  bmc1_merge_next_fun:                    0
% 1.99/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation
% 1.99/1.00  
% 1.99/1.00  inst_num_of_clauses:                    217
% 1.99/1.00  inst_num_in_passive:                    42
% 1.99/1.00  inst_num_in_active:                     164
% 1.99/1.00  inst_num_in_unprocessed:                11
% 1.99/1.00  inst_num_of_loops:                      170
% 1.99/1.00  inst_num_of_learning_restarts:          0
% 1.99/1.00  inst_num_moves_active_passive:          2
% 1.99/1.00  inst_lit_activity:                      0
% 1.99/1.00  inst_lit_activity_moves:                0
% 1.99/1.00  inst_num_tautologies:                   0
% 1.99/1.00  inst_num_prop_implied:                  0
% 1.99/1.00  inst_num_existing_simplified:           0
% 1.99/1.00  inst_num_eq_res_simplified:             0
% 1.99/1.00  inst_num_child_elim:                    0
% 1.99/1.00  inst_num_of_dismatching_blockings:      22
% 1.99/1.00  inst_num_of_non_proper_insts:           224
% 1.99/1.00  inst_num_of_duplicates:                 0
% 1.99/1.00  inst_inst_num_from_inst_to_res:         0
% 1.99/1.00  inst_dismatching_checking_time:         0.
% 1.99/1.00  
% 1.99/1.00  ------ Resolution
% 1.99/1.00  
% 1.99/1.00  res_num_of_clauses:                     0
% 1.99/1.00  res_num_in_passive:                     0
% 1.99/1.00  res_num_in_active:                      0
% 1.99/1.00  res_num_of_loops:                       121
% 1.99/1.00  res_forward_subset_subsumed:            44
% 1.99/1.00  res_backward_subset_subsumed:           0
% 1.99/1.00  res_forward_subsumed:                   0
% 1.99/1.00  res_backward_subsumed:                  0
% 1.99/1.00  res_forward_subsumption_resolution:     3
% 1.99/1.00  res_backward_subsumption_resolution:    0
% 1.99/1.00  res_clause_to_clause_subsumption:       129
% 1.99/1.00  res_orphan_elimination:                 0
% 1.99/1.00  res_tautology_del:                      23
% 1.99/1.00  res_num_eq_res_simplified:              0
% 1.99/1.00  res_num_sel_changes:                    0
% 1.99/1.00  res_moves_from_active_to_pass:          0
% 1.99/1.00  
% 1.99/1.00  ------ Superposition
% 1.99/1.00  
% 1.99/1.00  sup_time_total:                         0.
% 1.99/1.00  sup_time_generating:                    0.
% 1.99/1.00  sup_time_sim_full:                      0.
% 1.99/1.00  sup_time_sim_immed:                     0.
% 1.99/1.00  
% 1.99/1.00  sup_num_of_clauses:                     34
% 1.99/1.00  sup_num_in_active:                      28
% 1.99/1.00  sup_num_in_passive:                     6
% 1.99/1.00  sup_num_of_loops:                       33
% 1.99/1.00  sup_fw_superposition:                   18
% 1.99/1.00  sup_bw_superposition:                   7
% 1.99/1.00  sup_immediate_simplified:               1
% 1.99/1.00  sup_given_eliminated:                   0
% 1.99/1.00  comparisons_done:                       0
% 1.99/1.00  comparisons_avoided:                    0
% 1.99/1.00  
% 1.99/1.00  ------ Simplifications
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  sim_fw_subset_subsumed:                 2
% 1.99/1.00  sim_bw_subset_subsumed:                 3
% 1.99/1.00  sim_fw_subsumed:                        0
% 1.99/1.00  sim_bw_subsumed:                        0
% 1.99/1.00  sim_fw_subsumption_res:                 1
% 1.99/1.00  sim_bw_subsumption_res:                 0
% 1.99/1.00  sim_tautology_del:                      0
% 1.99/1.00  sim_eq_tautology_del:                   3
% 1.99/1.00  sim_eq_res_simp:                        0
% 1.99/1.00  sim_fw_demodulated:                     0
% 1.99/1.00  sim_bw_demodulated:                     5
% 1.99/1.00  sim_light_normalised:                   0
% 1.99/1.00  sim_joinable_taut:                      0
% 1.99/1.00  sim_joinable_simp:                      0
% 1.99/1.00  sim_ac_normalised:                      0
% 1.99/1.00  sim_smt_subsumption:                    0
% 1.99/1.00  
%------------------------------------------------------------------------------
