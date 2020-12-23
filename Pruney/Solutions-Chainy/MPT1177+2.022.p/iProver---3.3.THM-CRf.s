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
% DateTime   : Thu Dec  3 12:12:51 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  181 (1069 expanded)
%              Number of clauses        :  116 ( 215 expanded)
%              Number of leaves         :   19 ( 346 expanded)
%              Depth                    :   21
%              Number of atoms          :  915 (10085 expanded)
%              Number of equality atoms :  185 ( 266 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f24])).

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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f59,plain,(
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

fof(f65,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f68,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

cnf(c_957,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1412,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X2 != sK1
    | X0 != sK3
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_1470,plain,
    ( m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | X0 != sK3
    | X1 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_3837,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,X0,sK1)
    | X0 != sK0
    | sK1 != sK1
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_3839,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3837])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_10])).

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

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_734,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_147,c_22])).

cnf(c_735,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_739,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_26,c_25,c_24,c_23])).

cnf(c_1445,plain,
    ( ~ m1_orders_2(X0,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_3651,plain,
    ( ~ m1_orders_2(sK3,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1260,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1261,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_463,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_464,plain,
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
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_674,plain,
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
    inference(resolution_lifted,[status(thm)],[c_464,c_22])).

cnf(c_675,plain,
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
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | X0 = X1
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_26,c_25,c_24,c_23])).

cnf(c_851,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X0,sK0,X1)
    | m1_orders_2(X1,sK0,X0)
    | X0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_679])).

cnf(c_1252,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_2459,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1252])).

cnf(c_2736,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_2459])).

cnf(c_33,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_195,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_196,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_404,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_196])).

cnf(c_405,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_406,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1718,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_2259,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_2260,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_2745,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_33,c_34,c_406,c_2260])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_535,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_536,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_653,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_536,c_22])).

cnf(c_654,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_658,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_26,c_25,c_24,c_23])).

cnf(c_855,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_658])).

cnf(c_1251,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_758,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_759,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_761,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_759,c_26,c_25,c_24,c_23])).

cnf(c_1255,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_1519,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1255])).

cnf(c_1671,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1519])).

cnf(c_2755,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_1671])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_394,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_196])).

cnf(c_395,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_396,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1728,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2141,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_2142,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2141])).

cnf(c_3513,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_396,c_406,c_2142])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1262,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_502,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_503,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_586,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_503])).

cnf(c_587,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_629,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_22])).

cnf(c_630,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_26,c_25,c_24,c_23])).

cnf(c_859,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_634])).

cnf(c_1250,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | r1_tarski(X1,k4_xboole_0(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_1763,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1250])).

cnf(c_3275,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1763])).

cnf(c_3277,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3275])).

cnf(c_951,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1737,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_2275,plain,
    ( X0 = sK3
    | X0 != sK2
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_3048,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_956,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1407,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X2 != sK3
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_1775,plain,
    ( m1_orders_2(X0,X1,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X1 != sK0
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_2441,plain,
    ( m1_orders_2(sK3,X0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | X0 != sK0
    | sK3 != sK3
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_2443,plain,
    ( m1_orders_2(sK3,sK0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | sK3 != sK3
    | sK3 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_950,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1872,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1734,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1471,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1400,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1401,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_1384,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1385,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_193,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_194,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_381,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_194])).

cnf(c_382,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_383,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_70,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_66,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3839,c_3651,c_3513,c_3277,c_3048,c_2443,c_1872,c_1734,c_1471,c_1401,c_1385,c_1384,c_405,c_383,c_70,c_66,c_34,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.52/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.02  
% 2.52/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/1.02  
% 2.52/1.02  ------  iProver source info
% 2.52/1.02  
% 2.52/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.52/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/1.02  git: non_committed_changes: false
% 2.52/1.02  git: last_make_outside_of_git: false
% 2.52/1.02  
% 2.52/1.02  ------ 
% 2.52/1.02  
% 2.52/1.02  ------ Input Options
% 2.52/1.02  
% 2.52/1.02  --out_options                           all
% 2.52/1.02  --tptp_safe_out                         true
% 2.52/1.02  --problem_path                          ""
% 2.52/1.02  --include_path                          ""
% 2.52/1.02  --clausifier                            res/vclausify_rel
% 2.52/1.02  --clausifier_options                    --mode clausify
% 2.52/1.02  --stdin                                 false
% 2.52/1.02  --stats_out                             all
% 2.52/1.02  
% 2.52/1.02  ------ General Options
% 2.52/1.02  
% 2.52/1.02  --fof                                   false
% 2.52/1.02  --time_out_real                         305.
% 2.52/1.02  --time_out_virtual                      -1.
% 2.52/1.02  --symbol_type_check                     false
% 2.52/1.02  --clausify_out                          false
% 2.52/1.02  --sig_cnt_out                           false
% 2.52/1.02  --trig_cnt_out                          false
% 2.52/1.02  --trig_cnt_out_tolerance                1.
% 2.52/1.02  --trig_cnt_out_sk_spl                   false
% 2.52/1.02  --abstr_cl_out                          false
% 2.52/1.02  
% 2.52/1.02  ------ Global Options
% 2.52/1.02  
% 2.52/1.02  --schedule                              default
% 2.52/1.02  --add_important_lit                     false
% 2.52/1.02  --prop_solver_per_cl                    1000
% 2.52/1.02  --min_unsat_core                        false
% 2.52/1.02  --soft_assumptions                      false
% 2.52/1.02  --soft_lemma_size                       3
% 2.52/1.02  --prop_impl_unit_size                   0
% 2.52/1.02  --prop_impl_unit                        []
% 2.52/1.02  --share_sel_clauses                     true
% 2.52/1.02  --reset_solvers                         false
% 2.52/1.02  --bc_imp_inh                            [conj_cone]
% 2.52/1.02  --conj_cone_tolerance                   3.
% 2.52/1.02  --extra_neg_conj                        none
% 2.52/1.02  --large_theory_mode                     true
% 2.52/1.02  --prolific_symb_bound                   200
% 2.52/1.02  --lt_threshold                          2000
% 2.52/1.02  --clause_weak_htbl                      true
% 2.52/1.02  --gc_record_bc_elim                     false
% 2.52/1.02  
% 2.52/1.02  ------ Preprocessing Options
% 2.52/1.02  
% 2.52/1.02  --preprocessing_flag                    true
% 2.52/1.02  --time_out_prep_mult                    0.1
% 2.52/1.02  --splitting_mode                        input
% 2.52/1.02  --splitting_grd                         true
% 2.52/1.02  --splitting_cvd                         false
% 2.52/1.02  --splitting_cvd_svl                     false
% 2.52/1.02  --splitting_nvd                         32
% 2.52/1.02  --sub_typing                            true
% 2.52/1.02  --prep_gs_sim                           true
% 2.52/1.02  --prep_unflatten                        true
% 2.52/1.02  --prep_res_sim                          true
% 2.52/1.02  --prep_upred                            true
% 2.52/1.02  --prep_sem_filter                       exhaustive
% 2.52/1.02  --prep_sem_filter_out                   false
% 2.52/1.02  --pred_elim                             true
% 2.52/1.02  --res_sim_input                         true
% 2.52/1.02  --eq_ax_congr_red                       true
% 2.52/1.02  --pure_diseq_elim                       true
% 2.52/1.02  --brand_transform                       false
% 2.52/1.02  --non_eq_to_eq                          false
% 2.52/1.02  --prep_def_merge                        true
% 2.52/1.02  --prep_def_merge_prop_impl              false
% 2.52/1.02  --prep_def_merge_mbd                    true
% 2.52/1.02  --prep_def_merge_tr_red                 false
% 2.52/1.02  --prep_def_merge_tr_cl                  false
% 2.52/1.02  --smt_preprocessing                     true
% 2.52/1.02  --smt_ac_axioms                         fast
% 2.52/1.02  --preprocessed_out                      false
% 2.52/1.02  --preprocessed_stats                    false
% 2.52/1.02  
% 2.52/1.02  ------ Abstraction refinement Options
% 2.52/1.02  
% 2.52/1.02  --abstr_ref                             []
% 2.52/1.02  --abstr_ref_prep                        false
% 2.52/1.02  --abstr_ref_until_sat                   false
% 2.52/1.02  --abstr_ref_sig_restrict                funpre
% 2.52/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.02  --abstr_ref_under                       []
% 2.52/1.02  
% 2.52/1.02  ------ SAT Options
% 2.52/1.02  
% 2.52/1.02  --sat_mode                              false
% 2.52/1.02  --sat_fm_restart_options                ""
% 2.52/1.02  --sat_gr_def                            false
% 2.52/1.02  --sat_epr_types                         true
% 2.52/1.02  --sat_non_cyclic_types                  false
% 2.52/1.02  --sat_finite_models                     false
% 2.52/1.02  --sat_fm_lemmas                         false
% 2.52/1.02  --sat_fm_prep                           false
% 2.52/1.02  --sat_fm_uc_incr                        true
% 2.52/1.02  --sat_out_model                         small
% 2.52/1.02  --sat_out_clauses                       false
% 2.52/1.02  
% 2.52/1.02  ------ QBF Options
% 2.52/1.02  
% 2.52/1.02  --qbf_mode                              false
% 2.52/1.02  --qbf_elim_univ                         false
% 2.52/1.02  --qbf_dom_inst                          none
% 2.52/1.02  --qbf_dom_pre_inst                      false
% 2.52/1.02  --qbf_sk_in                             false
% 2.52/1.02  --qbf_pred_elim                         true
% 2.52/1.02  --qbf_split                             512
% 2.52/1.02  
% 2.52/1.02  ------ BMC1 Options
% 2.52/1.02  
% 2.52/1.02  --bmc1_incremental                      false
% 2.52/1.02  --bmc1_axioms                           reachable_all
% 2.52/1.02  --bmc1_min_bound                        0
% 2.52/1.02  --bmc1_max_bound                        -1
% 2.52/1.02  --bmc1_max_bound_default                -1
% 2.52/1.02  --bmc1_symbol_reachability              true
% 2.52/1.02  --bmc1_property_lemmas                  false
% 2.52/1.02  --bmc1_k_induction                      false
% 2.52/1.02  --bmc1_non_equiv_states                 false
% 2.52/1.02  --bmc1_deadlock                         false
% 2.52/1.02  --bmc1_ucm                              false
% 2.52/1.02  --bmc1_add_unsat_core                   none
% 2.52/1.02  --bmc1_unsat_core_children              false
% 2.52/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.02  --bmc1_out_stat                         full
% 2.52/1.02  --bmc1_ground_init                      false
% 2.52/1.02  --bmc1_pre_inst_next_state              false
% 2.52/1.02  --bmc1_pre_inst_state                   false
% 2.52/1.02  --bmc1_pre_inst_reach_state             false
% 2.52/1.02  --bmc1_out_unsat_core                   false
% 2.52/1.02  --bmc1_aig_witness_out                  false
% 2.52/1.02  --bmc1_verbose                          false
% 2.52/1.02  --bmc1_dump_clauses_tptp                false
% 2.52/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.02  --bmc1_dump_file                        -
% 2.52/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.02  --bmc1_ucm_extend_mode                  1
% 2.52/1.02  --bmc1_ucm_init_mode                    2
% 2.52/1.02  --bmc1_ucm_cone_mode                    none
% 2.52/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.02  --bmc1_ucm_relax_model                  4
% 2.52/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.02  --bmc1_ucm_layered_model                none
% 2.52/1.02  --bmc1_ucm_max_lemma_size               10
% 2.52/1.02  
% 2.52/1.02  ------ AIG Options
% 2.52/1.02  
% 2.52/1.02  --aig_mode                              false
% 2.52/1.02  
% 2.52/1.02  ------ Instantiation Options
% 2.52/1.02  
% 2.52/1.02  --instantiation_flag                    true
% 2.52/1.02  --inst_sos_flag                         false
% 2.52/1.02  --inst_sos_phase                        true
% 2.52/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.02  --inst_lit_sel_side                     num_symb
% 2.52/1.02  --inst_solver_per_active                1400
% 2.52/1.02  --inst_solver_calls_frac                1.
% 2.52/1.02  --inst_passive_queue_type               priority_queues
% 2.52/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.02  --inst_passive_queues_freq              [25;2]
% 2.52/1.02  --inst_dismatching                      true
% 2.52/1.02  --inst_eager_unprocessed_to_passive     true
% 2.52/1.02  --inst_prop_sim_given                   true
% 2.52/1.02  --inst_prop_sim_new                     false
% 2.52/1.02  --inst_subs_new                         false
% 2.52/1.02  --inst_eq_res_simp                      false
% 2.52/1.02  --inst_subs_given                       false
% 2.52/1.02  --inst_orphan_elimination               true
% 2.52/1.02  --inst_learning_loop_flag               true
% 2.52/1.02  --inst_learning_start                   3000
% 2.52/1.02  --inst_learning_factor                  2
% 2.52/1.02  --inst_start_prop_sim_after_learn       3
% 2.52/1.02  --inst_sel_renew                        solver
% 2.52/1.02  --inst_lit_activity_flag                true
% 2.52/1.02  --inst_restr_to_given                   false
% 2.52/1.02  --inst_activity_threshold               500
% 2.52/1.02  --inst_out_proof                        true
% 2.52/1.02  
% 2.52/1.02  ------ Resolution Options
% 2.52/1.02  
% 2.52/1.02  --resolution_flag                       true
% 2.52/1.02  --res_lit_sel                           adaptive
% 2.52/1.02  --res_lit_sel_side                      none
% 2.52/1.02  --res_ordering                          kbo
% 2.52/1.02  --res_to_prop_solver                    active
% 2.52/1.02  --res_prop_simpl_new                    false
% 2.52/1.02  --res_prop_simpl_given                  true
% 2.52/1.02  --res_passive_queue_type                priority_queues
% 2.52/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.02  --res_passive_queues_freq               [15;5]
% 2.52/1.02  --res_forward_subs                      full
% 2.52/1.02  --res_backward_subs                     full
% 2.52/1.02  --res_forward_subs_resolution           true
% 2.52/1.02  --res_backward_subs_resolution          true
% 2.52/1.02  --res_orphan_elimination                true
% 2.52/1.02  --res_time_limit                        2.
% 2.52/1.02  --res_out_proof                         true
% 2.52/1.02  
% 2.52/1.02  ------ Superposition Options
% 2.52/1.02  
% 2.52/1.02  --superposition_flag                    true
% 2.52/1.02  --sup_passive_queue_type                priority_queues
% 2.52/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.02  --demod_completeness_check              fast
% 2.52/1.02  --demod_use_ground                      true
% 2.52/1.02  --sup_to_prop_solver                    passive
% 2.52/1.02  --sup_prop_simpl_new                    true
% 2.52/1.02  --sup_prop_simpl_given                  true
% 2.52/1.02  --sup_fun_splitting                     false
% 2.52/1.02  --sup_smt_interval                      50000
% 2.52/1.02  
% 2.52/1.02  ------ Superposition Simplification Setup
% 2.52/1.02  
% 2.52/1.02  --sup_indices_passive                   []
% 2.52/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_full_bw                           [BwDemod]
% 2.52/1.02  --sup_immed_triv                        [TrivRules]
% 2.52/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_immed_bw_main                     []
% 2.52/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.02  
% 2.52/1.02  ------ Combination Options
% 2.52/1.02  
% 2.52/1.02  --comb_res_mult                         3
% 2.52/1.02  --comb_sup_mult                         2
% 2.52/1.02  --comb_inst_mult                        10
% 2.52/1.02  
% 2.52/1.02  ------ Debug Options
% 2.52/1.02  
% 2.52/1.02  --dbg_backtrace                         false
% 2.52/1.02  --dbg_dump_prop_clauses                 false
% 2.52/1.02  --dbg_dump_prop_clauses_file            -
% 2.52/1.02  --dbg_out_stat                          false
% 2.52/1.02  ------ Parsing...
% 2.52/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/1.02  
% 2.52/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.52/1.02  
% 2.52/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/1.02  
% 2.52/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/1.02  ------ Proving...
% 2.52/1.02  ------ Problem Properties 
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  clauses                                 16
% 2.52/1.02  conjectures                             2
% 2.52/1.02  EPR                                     10
% 2.52/1.02  Horn                                    14
% 2.52/1.02  unary                                   4
% 2.52/1.02  binary                                  4
% 2.52/1.02  lits                                    41
% 2.52/1.02  lits eq                                 6
% 2.52/1.02  fd_pure                                 0
% 2.52/1.02  fd_pseudo                               0
% 2.52/1.02  fd_cond                                 1
% 2.52/1.02  fd_pseudo_cond                          3
% 2.52/1.02  AC symbols                              0
% 2.52/1.02  
% 2.52/1.02  ------ Schedule dynamic 5 is on 
% 2.52/1.02  
% 2.52/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  ------ 
% 2.52/1.02  Current options:
% 2.52/1.02  ------ 
% 2.52/1.02  
% 2.52/1.02  ------ Input Options
% 2.52/1.02  
% 2.52/1.02  --out_options                           all
% 2.52/1.02  --tptp_safe_out                         true
% 2.52/1.02  --problem_path                          ""
% 2.52/1.02  --include_path                          ""
% 2.52/1.02  --clausifier                            res/vclausify_rel
% 2.52/1.02  --clausifier_options                    --mode clausify
% 2.52/1.02  --stdin                                 false
% 2.52/1.02  --stats_out                             all
% 2.52/1.02  
% 2.52/1.02  ------ General Options
% 2.52/1.02  
% 2.52/1.02  --fof                                   false
% 2.52/1.02  --time_out_real                         305.
% 2.52/1.02  --time_out_virtual                      -1.
% 2.52/1.02  --symbol_type_check                     false
% 2.52/1.02  --clausify_out                          false
% 2.52/1.02  --sig_cnt_out                           false
% 2.52/1.02  --trig_cnt_out                          false
% 2.52/1.02  --trig_cnt_out_tolerance                1.
% 2.52/1.02  --trig_cnt_out_sk_spl                   false
% 2.52/1.02  --abstr_cl_out                          false
% 2.52/1.02  
% 2.52/1.02  ------ Global Options
% 2.52/1.02  
% 2.52/1.02  --schedule                              default
% 2.52/1.02  --add_important_lit                     false
% 2.52/1.02  --prop_solver_per_cl                    1000
% 2.52/1.02  --min_unsat_core                        false
% 2.52/1.02  --soft_assumptions                      false
% 2.52/1.02  --soft_lemma_size                       3
% 2.52/1.02  --prop_impl_unit_size                   0
% 2.52/1.02  --prop_impl_unit                        []
% 2.52/1.02  --share_sel_clauses                     true
% 2.52/1.02  --reset_solvers                         false
% 2.52/1.02  --bc_imp_inh                            [conj_cone]
% 2.52/1.02  --conj_cone_tolerance                   3.
% 2.52/1.02  --extra_neg_conj                        none
% 2.52/1.02  --large_theory_mode                     true
% 2.52/1.02  --prolific_symb_bound                   200
% 2.52/1.02  --lt_threshold                          2000
% 2.52/1.02  --clause_weak_htbl                      true
% 2.52/1.02  --gc_record_bc_elim                     false
% 2.52/1.02  
% 2.52/1.02  ------ Preprocessing Options
% 2.52/1.02  
% 2.52/1.02  --preprocessing_flag                    true
% 2.52/1.02  --time_out_prep_mult                    0.1
% 2.52/1.02  --splitting_mode                        input
% 2.52/1.02  --splitting_grd                         true
% 2.52/1.02  --splitting_cvd                         false
% 2.52/1.02  --splitting_cvd_svl                     false
% 2.52/1.02  --splitting_nvd                         32
% 2.52/1.02  --sub_typing                            true
% 2.52/1.02  --prep_gs_sim                           true
% 2.52/1.02  --prep_unflatten                        true
% 2.52/1.02  --prep_res_sim                          true
% 2.52/1.02  --prep_upred                            true
% 2.52/1.02  --prep_sem_filter                       exhaustive
% 2.52/1.02  --prep_sem_filter_out                   false
% 2.52/1.02  --pred_elim                             true
% 2.52/1.02  --res_sim_input                         true
% 2.52/1.02  --eq_ax_congr_red                       true
% 2.52/1.02  --pure_diseq_elim                       true
% 2.52/1.02  --brand_transform                       false
% 2.52/1.02  --non_eq_to_eq                          false
% 2.52/1.02  --prep_def_merge                        true
% 2.52/1.02  --prep_def_merge_prop_impl              false
% 2.52/1.02  --prep_def_merge_mbd                    true
% 2.52/1.02  --prep_def_merge_tr_red                 false
% 2.52/1.02  --prep_def_merge_tr_cl                  false
% 2.52/1.02  --smt_preprocessing                     true
% 2.52/1.02  --smt_ac_axioms                         fast
% 2.52/1.02  --preprocessed_out                      false
% 2.52/1.02  --preprocessed_stats                    false
% 2.52/1.02  
% 2.52/1.02  ------ Abstraction refinement Options
% 2.52/1.02  
% 2.52/1.02  --abstr_ref                             []
% 2.52/1.02  --abstr_ref_prep                        false
% 2.52/1.02  --abstr_ref_until_sat                   false
% 2.52/1.02  --abstr_ref_sig_restrict                funpre
% 2.52/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.02  --abstr_ref_under                       []
% 2.52/1.02  
% 2.52/1.02  ------ SAT Options
% 2.52/1.02  
% 2.52/1.02  --sat_mode                              false
% 2.52/1.02  --sat_fm_restart_options                ""
% 2.52/1.02  --sat_gr_def                            false
% 2.52/1.02  --sat_epr_types                         true
% 2.52/1.02  --sat_non_cyclic_types                  false
% 2.52/1.02  --sat_finite_models                     false
% 2.52/1.02  --sat_fm_lemmas                         false
% 2.52/1.02  --sat_fm_prep                           false
% 2.52/1.02  --sat_fm_uc_incr                        true
% 2.52/1.02  --sat_out_model                         small
% 2.52/1.02  --sat_out_clauses                       false
% 2.52/1.02  
% 2.52/1.02  ------ QBF Options
% 2.52/1.02  
% 2.52/1.02  --qbf_mode                              false
% 2.52/1.02  --qbf_elim_univ                         false
% 2.52/1.02  --qbf_dom_inst                          none
% 2.52/1.02  --qbf_dom_pre_inst                      false
% 2.52/1.02  --qbf_sk_in                             false
% 2.52/1.02  --qbf_pred_elim                         true
% 2.52/1.02  --qbf_split                             512
% 2.52/1.02  
% 2.52/1.02  ------ BMC1 Options
% 2.52/1.02  
% 2.52/1.02  --bmc1_incremental                      false
% 2.52/1.02  --bmc1_axioms                           reachable_all
% 2.52/1.02  --bmc1_min_bound                        0
% 2.52/1.02  --bmc1_max_bound                        -1
% 2.52/1.02  --bmc1_max_bound_default                -1
% 2.52/1.02  --bmc1_symbol_reachability              true
% 2.52/1.02  --bmc1_property_lemmas                  false
% 2.52/1.02  --bmc1_k_induction                      false
% 2.52/1.02  --bmc1_non_equiv_states                 false
% 2.52/1.02  --bmc1_deadlock                         false
% 2.52/1.02  --bmc1_ucm                              false
% 2.52/1.02  --bmc1_add_unsat_core                   none
% 2.52/1.02  --bmc1_unsat_core_children              false
% 2.52/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.02  --bmc1_out_stat                         full
% 2.52/1.02  --bmc1_ground_init                      false
% 2.52/1.02  --bmc1_pre_inst_next_state              false
% 2.52/1.02  --bmc1_pre_inst_state                   false
% 2.52/1.02  --bmc1_pre_inst_reach_state             false
% 2.52/1.02  --bmc1_out_unsat_core                   false
% 2.52/1.02  --bmc1_aig_witness_out                  false
% 2.52/1.02  --bmc1_verbose                          false
% 2.52/1.02  --bmc1_dump_clauses_tptp                false
% 2.52/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.02  --bmc1_dump_file                        -
% 2.52/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.02  --bmc1_ucm_extend_mode                  1
% 2.52/1.02  --bmc1_ucm_init_mode                    2
% 2.52/1.02  --bmc1_ucm_cone_mode                    none
% 2.52/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.02  --bmc1_ucm_relax_model                  4
% 2.52/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.02  --bmc1_ucm_layered_model                none
% 2.52/1.02  --bmc1_ucm_max_lemma_size               10
% 2.52/1.02  
% 2.52/1.02  ------ AIG Options
% 2.52/1.02  
% 2.52/1.02  --aig_mode                              false
% 2.52/1.02  
% 2.52/1.02  ------ Instantiation Options
% 2.52/1.02  
% 2.52/1.02  --instantiation_flag                    true
% 2.52/1.02  --inst_sos_flag                         false
% 2.52/1.02  --inst_sos_phase                        true
% 2.52/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.02  --inst_lit_sel_side                     none
% 2.52/1.02  --inst_solver_per_active                1400
% 2.52/1.02  --inst_solver_calls_frac                1.
% 2.52/1.02  --inst_passive_queue_type               priority_queues
% 2.52/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.02  --inst_passive_queues_freq              [25;2]
% 2.52/1.02  --inst_dismatching                      true
% 2.52/1.02  --inst_eager_unprocessed_to_passive     true
% 2.52/1.02  --inst_prop_sim_given                   true
% 2.52/1.02  --inst_prop_sim_new                     false
% 2.52/1.02  --inst_subs_new                         false
% 2.52/1.02  --inst_eq_res_simp                      false
% 2.52/1.02  --inst_subs_given                       false
% 2.52/1.02  --inst_orphan_elimination               true
% 2.52/1.02  --inst_learning_loop_flag               true
% 2.52/1.02  --inst_learning_start                   3000
% 2.52/1.02  --inst_learning_factor                  2
% 2.52/1.02  --inst_start_prop_sim_after_learn       3
% 2.52/1.02  --inst_sel_renew                        solver
% 2.52/1.02  --inst_lit_activity_flag                true
% 2.52/1.02  --inst_restr_to_given                   false
% 2.52/1.02  --inst_activity_threshold               500
% 2.52/1.02  --inst_out_proof                        true
% 2.52/1.02  
% 2.52/1.02  ------ Resolution Options
% 2.52/1.02  
% 2.52/1.02  --resolution_flag                       false
% 2.52/1.02  --res_lit_sel                           adaptive
% 2.52/1.02  --res_lit_sel_side                      none
% 2.52/1.02  --res_ordering                          kbo
% 2.52/1.02  --res_to_prop_solver                    active
% 2.52/1.02  --res_prop_simpl_new                    false
% 2.52/1.02  --res_prop_simpl_given                  true
% 2.52/1.02  --res_passive_queue_type                priority_queues
% 2.52/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.02  --res_passive_queues_freq               [15;5]
% 2.52/1.02  --res_forward_subs                      full
% 2.52/1.02  --res_backward_subs                     full
% 2.52/1.02  --res_forward_subs_resolution           true
% 2.52/1.02  --res_backward_subs_resolution          true
% 2.52/1.02  --res_orphan_elimination                true
% 2.52/1.02  --res_time_limit                        2.
% 2.52/1.02  --res_out_proof                         true
% 2.52/1.02  
% 2.52/1.02  ------ Superposition Options
% 2.52/1.02  
% 2.52/1.02  --superposition_flag                    true
% 2.52/1.02  --sup_passive_queue_type                priority_queues
% 2.52/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.02  --demod_completeness_check              fast
% 2.52/1.02  --demod_use_ground                      true
% 2.52/1.02  --sup_to_prop_solver                    passive
% 2.52/1.02  --sup_prop_simpl_new                    true
% 2.52/1.02  --sup_prop_simpl_given                  true
% 2.52/1.02  --sup_fun_splitting                     false
% 2.52/1.02  --sup_smt_interval                      50000
% 2.52/1.02  
% 2.52/1.02  ------ Superposition Simplification Setup
% 2.52/1.02  
% 2.52/1.02  --sup_indices_passive                   []
% 2.52/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_full_bw                           [BwDemod]
% 2.52/1.02  --sup_immed_triv                        [TrivRules]
% 2.52/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_immed_bw_main                     []
% 2.52/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.02  
% 2.52/1.02  ------ Combination Options
% 2.52/1.02  
% 2.52/1.02  --comb_res_mult                         3
% 2.52/1.02  --comb_sup_mult                         2
% 2.52/1.02  --comb_inst_mult                        10
% 2.52/1.02  
% 2.52/1.02  ------ Debug Options
% 2.52/1.02  
% 2.52/1.02  --dbg_backtrace                         false
% 2.52/1.02  --dbg_dump_prop_clauses                 false
% 2.52/1.02  --dbg_dump_prop_clauses_file            -
% 2.52/1.02  --dbg_out_stat                          false
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  ------ Proving...
% 2.52/1.02  
% 2.52/1.02  
% 2.52/1.02  % SZS status Theorem for theBenchmark.p
% 2.52/1.02  
% 2.52/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/1.02  
% 2.52/1.02  fof(f9,axiom,(
% 2.52/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f23,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f9])).
% 2.52/1.02  
% 2.52/1.02  fof(f24,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f23])).
% 2.52/1.02  
% 2.52/1.02  fof(f56,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f24])).
% 2.52/1.02  
% 2.52/1.02  fof(f6,axiom,(
% 2.52/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f17,plain,(
% 2.52/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f6])).
% 2.52/1.02  
% 2.52/1.02  fof(f18,plain,(
% 2.52/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f17])).
% 2.52/1.02  
% 2.52/1.02  fof(f53,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f18])).
% 2.52/1.02  
% 2.52/1.02  fof(f12,conjecture,(
% 2.52/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f13,negated_conjecture,(
% 2.52/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.52/1.02    inference(negated_conjecture,[],[f12])).
% 2.52/1.02  
% 2.52/1.02  fof(f29,plain,(
% 2.52/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f13])).
% 2.52/1.02  
% 2.52/1.02  fof(f30,plain,(
% 2.52/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f29])).
% 2.52/1.02  
% 2.52/1.02  fof(f36,plain,(
% 2.52/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.52/1.02    inference(nnf_transformation,[],[f30])).
% 2.52/1.02  
% 2.52/1.02  fof(f37,plain,(
% 2.52/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f36])).
% 2.52/1.02  
% 2.52/1.02  fof(f41,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.52/1.02    introduced(choice_axiom,[])).
% 2.52/1.02  
% 2.52/1.02  fof(f40,plain,(
% 2.52/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.52/1.02    introduced(choice_axiom,[])).
% 2.52/1.02  
% 2.52/1.02  fof(f39,plain,(
% 2.52/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.52/1.02    introduced(choice_axiom,[])).
% 2.52/1.02  
% 2.52/1.02  fof(f38,plain,(
% 2.52/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.52/1.02    introduced(choice_axiom,[])).
% 2.52/1.02  
% 2.52/1.02  fof(f42,plain,(
% 2.52/1.02    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.52/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40,f39,f38])).
% 2.52/1.02  
% 2.52/1.02  fof(f64,plain,(
% 2.52/1.02    l1_orders_2(sK0)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f60,plain,(
% 2.52/1.02    ~v2_struct_0(sK0)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f61,plain,(
% 2.52/1.02    v3_orders_2(sK0)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f62,plain,(
% 2.52/1.02    v4_orders_2(sK0)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f63,plain,(
% 2.52/1.02    v5_orders_2(sK0)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f66,plain,(
% 2.52/1.02    m2_orders_2(sK2,sK0,sK1)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f67,plain,(
% 2.52/1.02    m2_orders_2(sK3,sK0,sK1)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f11,axiom,(
% 2.52/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f27,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f11])).
% 2.52/1.02  
% 2.52/1.02  fof(f28,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f27])).
% 2.52/1.02  
% 2.52/1.02  fof(f35,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(nnf_transformation,[],[f28])).
% 2.52/1.02  
% 2.52/1.02  fof(f59,plain,(
% 2.52/1.02    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f35])).
% 2.52/1.02  
% 2.52/1.02  fof(f65,plain,(
% 2.52/1.02    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f1,axiom,(
% 2.52/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f31,plain,(
% 2.52/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.52/1.02    inference(nnf_transformation,[],[f1])).
% 2.52/1.02  
% 2.52/1.02  fof(f32,plain,(
% 2.52/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.52/1.02    inference(flattening,[],[f31])).
% 2.52/1.02  
% 2.52/1.02  fof(f44,plain,(
% 2.52/1.02    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f32])).
% 2.52/1.02  
% 2.52/1.02  fof(f70,plain,(
% 2.52/1.02    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.52/1.02    inference(equality_resolution,[],[f44])).
% 2.52/1.02  
% 2.52/1.02  fof(f68,plain,(
% 2.52/1.02    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f7,axiom,(
% 2.52/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f15,plain,(
% 2.52/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.02    inference(pure_predicate_removal,[],[f7])).
% 2.52/1.02  
% 2.52/1.02  fof(f19,plain,(
% 2.52/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f15])).
% 2.52/1.02  
% 2.52/1.02  fof(f20,plain,(
% 2.52/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f19])).
% 2.52/1.02  
% 2.52/1.02  fof(f54,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f20])).
% 2.52/1.02  
% 2.52/1.02  fof(f8,axiom,(
% 2.52/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f21,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f8])).
% 2.52/1.02  
% 2.52/1.02  fof(f22,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f21])).
% 2.52/1.02  
% 2.52/1.02  fof(f55,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f22])).
% 2.52/1.02  
% 2.52/1.02  fof(f43,plain,(
% 2.52/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f32])).
% 2.52/1.02  
% 2.52/1.02  fof(f3,axiom,(
% 2.52/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f33,plain,(
% 2.52/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.52/1.02    inference(nnf_transformation,[],[f3])).
% 2.52/1.02  
% 2.52/1.02  fof(f34,plain,(
% 2.52/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.52/1.02    inference(flattening,[],[f33])).
% 2.52/1.02  
% 2.52/1.02  fof(f49,plain,(
% 2.52/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f34])).
% 2.52/1.02  
% 2.52/1.02  fof(f5,axiom,(
% 2.52/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f52,plain,(
% 2.52/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f5])).
% 2.52/1.02  
% 2.52/1.02  fof(f4,axiom,(
% 2.52/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f16,plain,(
% 2.52/1.02    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.52/1.02    inference(ennf_transformation,[],[f4])).
% 2.52/1.02  
% 2.52/1.02  fof(f51,plain,(
% 2.52/1.02    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.52/1.02    inference(cnf_transformation,[],[f16])).
% 2.52/1.02  
% 2.52/1.02  fof(f10,axiom,(
% 2.52/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.52/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.02  
% 2.52/1.02  fof(f25,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/1.02    inference(ennf_transformation,[],[f10])).
% 2.52/1.02  
% 2.52/1.02  fof(f26,plain,(
% 2.52/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.52/1.02    inference(flattening,[],[f25])).
% 2.52/1.02  
% 2.52/1.02  fof(f57,plain,(
% 2.52/1.02    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f26])).
% 2.52/1.02  
% 2.52/1.02  fof(f45,plain,(
% 2.52/1.02    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.52/1.02    inference(cnf_transformation,[],[f32])).
% 2.52/1.02  
% 2.52/1.02  fof(f69,plain,(
% 2.52/1.02    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.52/1.02    inference(cnf_transformation,[],[f42])).
% 2.52/1.02  
% 2.52/1.02  fof(f47,plain,(
% 2.52/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.52/1.02    inference(cnf_transformation,[],[f34])).
% 2.52/1.02  
% 2.52/1.02  fof(f72,plain,(
% 2.52/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.52/1.02    inference(equality_resolution,[],[f47])).
% 2.52/1.02  
% 2.52/1.02  cnf(c_957,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.02      | m2_orders_2(X3,X4,X5)
% 2.52/1.02      | X3 != X0
% 2.52/1.02      | X4 != X1
% 2.52/1.02      | X5 != X2 ),
% 2.52/1.02      theory(equality) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_1412,plain,
% 2.52/1.02      ( m2_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.02      | X2 != sK1
% 2.52/1.02      | X0 != sK3
% 2.52/1.02      | X1 != sK0 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_957]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_1470,plain,
% 2.52/1.02      ( m2_orders_2(X0,X1,sK1)
% 2.52/1.02      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.02      | X0 != sK3
% 2.52/1.02      | X1 != sK0
% 2.52/1.02      | sK1 != sK1 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_1412]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_3837,plain,
% 2.52/1.02      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.02      | m2_orders_2(k1_xboole_0,X0,sK1)
% 2.52/1.02      | X0 != sK0
% 2.52/1.02      | sK1 != sK1
% 2.52/1.02      | k1_xboole_0 != sK3 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_1470]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_3839,plain,
% 2.52/1.02      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.02      | m2_orders_2(k1_xboole_0,sK0,sK1)
% 2.52/1.02      | sK1 != sK1
% 2.52/1.02      | sK0 != sK0
% 2.52/1.02      | k1_xboole_0 != sK3 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_3837]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_13,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.52/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | k1_xboole_0 = X2 ),
% 2.52/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_10,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1) ),
% 2.52/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_146,plain,
% 2.52/1.02      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.52/1.02      | ~ m1_orders_2(X0,X1,X2)
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | k1_xboole_0 = X2 ),
% 2.52/1.02      inference(global_propositional_subsumption,
% 2.52/1.02                [status(thm)],
% 2.52/1.02                [c_13,c_10]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_147,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.52/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | k1_xboole_0 = X2 ),
% 2.52/1.02      inference(renaming,[status(thm)],[c_146]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_22,negated_conjecture,
% 2.52/1.02      ( l1_orders_2(sK0) ),
% 2.52/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_734,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.52/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | sK0 != X1
% 2.52/1.02      | k1_xboole_0 = X2 ),
% 2.52/1.02      inference(resolution_lifted,[status(thm)],[c_147,c_22]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_735,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,sK0,X1)
% 2.52/1.02      | ~ m1_orders_2(X1,sK0,X0)
% 2.52/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.02      | v2_struct_0(sK0)
% 2.52/1.02      | ~ v3_orders_2(sK0)
% 2.52/1.02      | ~ v4_orders_2(sK0)
% 2.52/1.02      | ~ v5_orders_2(sK0)
% 2.52/1.02      | k1_xboole_0 = X0 ),
% 2.52/1.02      inference(unflattening,[status(thm)],[c_734]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_26,negated_conjecture,
% 2.52/1.02      ( ~ v2_struct_0(sK0) ),
% 2.52/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_25,negated_conjecture,
% 2.52/1.02      ( v3_orders_2(sK0) ),
% 2.52/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_24,negated_conjecture,
% 2.52/1.02      ( v4_orders_2(sK0) ),
% 2.52/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_23,negated_conjecture,
% 2.52/1.02      ( v5_orders_2(sK0) ),
% 2.52/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_739,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,sK0,X1)
% 2.52/1.02      | ~ m1_orders_2(X1,sK0,X0)
% 2.52/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.02      | k1_xboole_0 = X0 ),
% 2.52/1.02      inference(global_propositional_subsumption,
% 2.52/1.02                [status(thm)],
% 2.52/1.02                [c_735,c_26,c_25,c_24,c_23]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_1445,plain,
% 2.52/1.02      ( ~ m1_orders_2(X0,sK0,sK3)
% 2.52/1.02      | ~ m1_orders_2(sK3,sK0,X0)
% 2.52/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.02      | k1_xboole_0 = sK3 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_739]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_3651,plain,
% 2.52/1.02      ( ~ m1_orders_2(sK3,sK0,sK3)
% 2.52/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.02      | k1_xboole_0 = sK3 ),
% 2.52/1.02      inference(instantiation,[status(thm)],[c_1445]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_20,negated_conjecture,
% 2.52/1.02      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.52/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_1260,plain,
% 2.52/1.02      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.52/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_19,negated_conjecture,
% 2.52/1.02      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.52/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_1261,plain,
% 2.52/1.02      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.52/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_15,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.52/1.02      | m1_orders_2(X3,X1,X0)
% 2.52/1.02      | m1_orders_2(X0,X1,X3)
% 2.52/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | X3 = X0 ),
% 2.52/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_21,negated_conjecture,
% 2.52/1.02      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.52/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_463,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.52/1.02      | m1_orders_2(X3,X1,X0)
% 2.52/1.02      | m1_orders_2(X0,X1,X3)
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | X3 = X0
% 2.52/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.02      | sK1 != X2 ),
% 2.52/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_464,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.02      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.02      | m1_orders_2(X0,X1,X2)
% 2.52/1.02      | m1_orders_2(X2,X1,X0)
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | ~ l1_orders_2(X1)
% 2.52/1.02      | X0 = X2
% 2.52/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.02      inference(unflattening,[status(thm)],[c_463]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_674,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.02      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.02      | m1_orders_2(X0,X1,X2)
% 2.52/1.02      | m1_orders_2(X2,X1,X0)
% 2.52/1.02      | v2_struct_0(X1)
% 2.52/1.02      | ~ v3_orders_2(X1)
% 2.52/1.02      | ~ v4_orders_2(X1)
% 2.52/1.02      | ~ v5_orders_2(X1)
% 2.52/1.02      | X2 = X0
% 2.52/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.02      | sK0 != X1 ),
% 2.52/1.02      inference(resolution_lifted,[status(thm)],[c_464,c_22]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_675,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.02      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.02      | m1_orders_2(X0,sK0,X1)
% 2.52/1.02      | m1_orders_2(X1,sK0,X0)
% 2.52/1.02      | v2_struct_0(sK0)
% 2.52/1.02      | ~ v3_orders_2(sK0)
% 2.52/1.02      | ~ v4_orders_2(sK0)
% 2.52/1.02      | ~ v5_orders_2(sK0)
% 2.52/1.02      | X0 = X1
% 2.52/1.02      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.02      inference(unflattening,[status(thm)],[c_674]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_679,plain,
% 2.52/1.02      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.02      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.02      | m1_orders_2(X0,sK0,X1)
% 2.52/1.02      | m1_orders_2(X1,sK0,X0)
% 2.52/1.02      | X0 = X1
% 2.52/1.02      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.02      inference(global_propositional_subsumption,
% 2.52/1.02                [status(thm)],
% 2.52/1.02                [c_675,c_26,c_25,c_24,c_23]) ).
% 2.52/1.02  
% 2.52/1.02  cnf(c_851,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.03      | m1_orders_2(X0,sK0,X1)
% 2.52/1.03      | m1_orders_2(X1,sK0,X0)
% 2.52/1.03      | X0 = X1 ),
% 2.52/1.03      inference(equality_resolution_simp,[status(thm)],[c_679]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1252,plain,
% 2.52/1.03      ( X0 = X1
% 2.52/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.52/1.03      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2459,plain,
% 2.52/1.03      ( sK3 = X0
% 2.52/1.03      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.52/1.03      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1261,c_1252]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2736,plain,
% 2.52/1.03      ( sK3 = sK2
% 2.52/1.03      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.52/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1260,c_2459]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_33,plain,
% 2.52/1.03      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_34,plain,
% 2.52/1.03      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1,plain,
% 2.52/1.03      ( ~ r2_xboole_0(X0,X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_18,negated_conjecture,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.52/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_195,plain,
% 2.52/1.03      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.52/1.03      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_196,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.52/1.03      inference(renaming,[status(thm)],[c_195]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_404,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_196]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_405,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_404]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_406,plain,
% 2.52/1.03      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1718,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.03      | m1_orders_2(X0,sK0,sK3)
% 2.52/1.03      | m1_orders_2(sK3,sK0,X0)
% 2.52/1.03      | X0 = sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_851]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2259,plain,
% 2.52/1.03      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.52/1.03      | m1_orders_2(sK3,sK0,sK2)
% 2.52/1.03      | m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | sK2 = sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_1718]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2260,plain,
% 2.52/1.03      ( sK2 = sK3
% 2.52/1.03      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.52/1.03      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.52/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_2259]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2745,plain,
% 2.52/1.03      ( m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.52/1.03      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_2736,c_33,c_34,c_406,c_2260]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_11,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_535,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.03      | sK1 != X2 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_536,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_535]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_653,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.03      | sK0 != X1 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_536,c_22]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_654,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.03      | v2_struct_0(sK0)
% 2.52/1.03      | ~ v3_orders_2(sK0)
% 2.52/1.03      | ~ v4_orders_2(sK0)
% 2.52/1.03      | ~ v5_orders_2(sK0)
% 2.52/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_653]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_658,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_654,c_26,c_25,c_24,c_23]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_855,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.52/1.03      inference(equality_resolution_simp,[status(thm)],[c_658]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1251,plain,
% 2.52/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_12,plain,
% 2.52/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | r1_tarski(X0,X2)
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_758,plain,
% 2.52/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | r1_tarski(X0,X2)
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | sK0 != X1 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_759,plain,
% 2.52/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.52/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.03      | r1_tarski(X0,X1)
% 2.52/1.03      | v2_struct_0(sK0)
% 2.52/1.03      | ~ v3_orders_2(sK0)
% 2.52/1.03      | ~ v4_orders_2(sK0)
% 2.52/1.03      | ~ v5_orders_2(sK0) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_758]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_761,plain,
% 2.52/1.03      ( ~ m1_orders_2(X0,sK0,X1)
% 2.52/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.03      | r1_tarski(X0,X1) ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_759,c_26,c_25,c_24,c_23]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1255,plain,
% 2.52/1.03      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.52/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.52/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1519,plain,
% 2.52/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.52/1.03      | r1_tarski(X1,X0) = iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1251,c_1255]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1671,plain,
% 2.52/1.03      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.52/1.03      | r1_tarski(X0,sK2) = iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1260,c_1519]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2755,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.52/1.03      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_2745,c_1671]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2,plain,
% 2.52/1.03      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_394,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | r1_tarski(X0,X1)
% 2.52/1.03      | sK3 != X1
% 2.52/1.03      | sK2 != X0 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_196]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_395,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_394]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_396,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.52/1.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_4,plain,
% 2.52/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.52/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1728,plain,
% 2.52/1.03      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2141,plain,
% 2.52/1.03      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_1728]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2142,plain,
% 2.52/1.03      ( sK2 = sK3
% 2.52/1.03      | r1_tarski(sK3,sK2) != iProver_top
% 2.52/1.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_2141]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_3513,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_2755,c_396,c_406,c_2142]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_9,plain,
% 2.52/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1262,plain,
% 2.52/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_7,plain,
% 2.52/1.03      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 2.52/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_14,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.52/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.52/1.03      | ~ r1_xboole_0(X0,X3)
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_502,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m2_orders_2(X3,X1,X2)
% 2.52/1.03      | ~ r1_xboole_0(X0,X3)
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.03      | sK1 != X2 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_503,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.03      | ~ r1_xboole_0(X2,X0)
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_502]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_586,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.03      | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | X2 != X3
% 2.52/1.03      | X0 != X5
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_503]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_587,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.03      | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | ~ l1_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_586]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_629,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,X1,sK1)
% 2.52/1.03      | ~ m2_orders_2(X2,X1,sK1)
% 2.52/1.03      | ~ r1_tarski(X0,k4_xboole_0(X3,X2))
% 2.52/1.03      | v2_struct_0(X1)
% 2.52/1.03      | ~ v3_orders_2(X1)
% 2.52/1.03      | ~ v4_orders_2(X1)
% 2.52/1.03      | ~ v5_orders_2(X1)
% 2.52/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.52/1.03      | sK0 != X1 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_587,c_22]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_630,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.03      | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
% 2.52/1.03      | v2_struct_0(sK0)
% 2.52/1.03      | ~ v3_orders_2(sK0)
% 2.52/1.03      | ~ v4_orders_2(sK0)
% 2.52/1.03      | ~ v5_orders_2(sK0)
% 2.52/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_629]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_634,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.03      | ~ r1_tarski(X1,k4_xboole_0(X2,X0))
% 2.52/1.03      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_630,c_26,c_25,c_24,c_23]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_859,plain,
% 2.52/1.03      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.52/1.03      | ~ m2_orders_2(X1,sK0,sK1)
% 2.52/1.03      | ~ r1_tarski(X1,k4_xboole_0(X2,X0)) ),
% 2.52/1.03      inference(equality_resolution_simp,[status(thm)],[c_634]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1250,plain,
% 2.52/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.52/1.03      | r1_tarski(X1,k4_xboole_0(X2,X0)) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1763,plain,
% 2.52/1.03      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.52/1.03      | m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1262,c_1250]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_3275,plain,
% 2.52/1.03      ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1261,c_1763]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_3277,plain,
% 2.52/1.03      ( ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
% 2.52/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3275]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_951,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1737,plain,
% 2.52/1.03      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_951]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2275,plain,
% 2.52/1.03      ( X0 = sK3 | X0 != sK2 | sK3 != sK2 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_1737]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_3048,plain,
% 2.52/1.03      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_2275]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_956,plain,
% 2.52/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 2.52/1.03      | m1_orders_2(X3,X4,X5)
% 2.52/1.03      | X3 != X0
% 2.52/1.03      | X4 != X1
% 2.52/1.03      | X5 != X2 ),
% 2.52/1.03      theory(equality) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1407,plain,
% 2.52/1.03      ( m1_orders_2(X0,X1,X2)
% 2.52/1.03      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | X2 != sK3
% 2.52/1.03      | X1 != sK0
% 2.52/1.03      | X0 != sK2 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_956]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1775,plain,
% 2.52/1.03      ( m1_orders_2(X0,X1,sK3)
% 2.52/1.03      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | X1 != sK0
% 2.52/1.03      | X0 != sK2
% 2.52/1.03      | sK3 != sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_1407]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2441,plain,
% 2.52/1.03      ( m1_orders_2(sK3,X0,sK3)
% 2.52/1.03      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | X0 != sK0
% 2.52/1.03      | sK3 != sK3
% 2.52/1.03      | sK3 != sK2 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_1775]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2443,plain,
% 2.52/1.03      ( m1_orders_2(sK3,sK0,sK3)
% 2.52/1.03      | ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | sK3 != sK3
% 2.52/1.03      | sK3 != sK2
% 2.52/1.03      | sK0 != sK0 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_2441]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_950,plain,( X0 = X0 ),theory(equality) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1872,plain,
% 2.52/1.03      ( sK2 = sK2 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_950]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1734,plain,
% 2.52/1.03      ( sK3 = sK3 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_950]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1471,plain,
% 2.52/1.03      ( sK1 = sK1 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_950]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1400,plain,
% 2.52/1.03      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.52/1.03      | r1_tarski(sK2,sK3) ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_761]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1401,plain,
% 2.52/1.03      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.52/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.52/1.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1384,plain,
% 2.52/1.03      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.52/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_855]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1385,plain,
% 2.52/1.03      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.52/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_0,plain,
% 2.52/1.03      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.52/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_17,negated_conjecture,
% 2.52/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.52/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_193,plain,
% 2.52/1.03      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.52/1.03      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_194,plain,
% 2.52/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.52/1.03      inference(renaming,[status(thm)],[c_193]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_381,plain,
% 2.52/1.03      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.52/1.03      | ~ r1_tarski(X0,X1)
% 2.52/1.03      | X1 = X0
% 2.52/1.03      | sK3 != X1
% 2.52/1.03      | sK2 != X0 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_194]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_382,plain,
% 2.52/1.03      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_381]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_383,plain,
% 2.52/1.03      ( sK3 = sK2
% 2.52/1.03      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.52/1.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_70,plain,
% 2.52/1.03      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_6,plain,
% 2.52/1.03      ( r1_tarski(X0,X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_66,plain,
% 2.52/1.03      ( r1_tarski(sK0,sK0) ),
% 2.52/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(contradiction,plain,
% 2.52/1.03      ( $false ),
% 2.52/1.03      inference(minisat,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_3839,c_3651,c_3513,c_3277,c_3048,c_2443,c_1872,c_1734,
% 2.52/1.03                 c_1471,c_1401,c_1385,c_1384,c_405,c_383,c_70,c_66,c_34,
% 2.52/1.03                 c_19]) ).
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/1.03  
% 2.52/1.03  ------                               Statistics
% 2.52/1.03  
% 2.52/1.03  ------ General
% 2.52/1.03  
% 2.52/1.03  abstr_ref_over_cycles:                  0
% 2.52/1.03  abstr_ref_under_cycles:                 0
% 2.52/1.03  gc_basic_clause_elim:                   0
% 2.52/1.03  forced_gc_time:                         0
% 2.52/1.03  parsing_time:                           0.011
% 2.52/1.03  unif_index_cands_time:                  0.
% 2.52/1.03  unif_index_add_time:                    0.
% 2.52/1.03  orderings_time:                         0.
% 2.52/1.03  out_proof_time:                         0.017
% 2.52/1.03  total_time:                             0.162
% 2.52/1.03  num_of_symbols:                         52
% 2.52/1.03  num_of_terms:                           2574
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing
% 2.52/1.03  
% 2.52/1.03  num_of_splits:                          0
% 2.52/1.03  num_of_split_atoms:                     0
% 2.52/1.03  num_of_reused_defs:                     0
% 2.52/1.03  num_eq_ax_congr_red:                    11
% 2.52/1.03  num_of_sem_filtered_clauses:            1
% 2.52/1.03  num_of_subtypes:                        0
% 2.52/1.03  monotx_restored_types:                  0
% 2.52/1.03  sat_num_of_epr_types:                   0
% 2.52/1.03  sat_num_of_non_cyclic_types:            0
% 2.52/1.03  sat_guarded_non_collapsed_types:        0
% 2.52/1.03  num_pure_diseq_elim:                    0
% 2.52/1.03  simp_replaced_by:                       0
% 2.52/1.03  res_preprocessed:                       90
% 2.52/1.03  prep_upred:                             0
% 2.52/1.03  prep_unflattend:                        22
% 2.52/1.03  smt_new_axioms:                         0
% 2.52/1.03  pred_elim_cands:                        4
% 2.52/1.03  pred_elim:                              8
% 2.52/1.03  pred_elim_cl:                           9
% 2.52/1.03  pred_elim_cycles:                       11
% 2.52/1.03  merged_defs:                            2
% 2.52/1.03  merged_defs_ncl:                        0
% 2.52/1.03  bin_hyper_res:                          2
% 2.52/1.03  prep_cycles:                            4
% 2.52/1.03  pred_elim_time:                         0.011
% 2.52/1.03  splitting_time:                         0.
% 2.52/1.03  sem_filter_time:                        0.
% 2.52/1.03  monotx_time:                            0.
% 2.52/1.03  subtype_inf_time:                       0.
% 2.52/1.03  
% 2.52/1.03  ------ Problem properties
% 2.52/1.03  
% 2.52/1.03  clauses:                                16
% 2.52/1.03  conjectures:                            2
% 2.52/1.03  epr:                                    10
% 2.52/1.03  horn:                                   14
% 2.52/1.03  ground:                                 5
% 2.52/1.03  unary:                                  4
% 2.52/1.03  binary:                                 4
% 2.52/1.03  lits:                                   41
% 2.52/1.03  lits_eq:                                6
% 2.52/1.03  fd_pure:                                0
% 2.52/1.03  fd_pseudo:                              0
% 2.52/1.03  fd_cond:                                1
% 2.52/1.03  fd_pseudo_cond:                         3
% 2.52/1.03  ac_symbols:                             0
% 2.52/1.03  
% 2.52/1.03  ------ Propositional Solver
% 2.52/1.03  
% 2.52/1.03  prop_solver_calls:                      29
% 2.52/1.03  prop_fast_solver_calls:                 821
% 2.52/1.03  smt_solver_calls:                       0
% 2.52/1.03  smt_fast_solver_calls:                  0
% 2.52/1.03  prop_num_of_clauses:                    1339
% 2.52/1.03  prop_preprocess_simplified:             3859
% 2.52/1.03  prop_fo_subsumed:                       35
% 2.52/1.03  prop_solver_time:                       0.
% 2.52/1.03  smt_solver_time:                        0.
% 2.52/1.03  smt_fast_solver_time:                   0.
% 2.52/1.03  prop_fast_solver_time:                  0.
% 2.52/1.03  prop_unsat_core_time:                   0.
% 2.52/1.03  
% 2.52/1.03  ------ QBF
% 2.52/1.03  
% 2.52/1.03  qbf_q_res:                              0
% 2.52/1.03  qbf_num_tautologies:                    0
% 2.52/1.03  qbf_prep_cycles:                        0
% 2.52/1.03  
% 2.52/1.03  ------ BMC1
% 2.52/1.03  
% 2.52/1.03  bmc1_current_bound:                     -1
% 2.52/1.03  bmc1_last_solved_bound:                 -1
% 2.52/1.03  bmc1_unsat_core_size:                   -1
% 2.52/1.03  bmc1_unsat_core_parents_size:           -1
% 2.52/1.03  bmc1_merge_next_fun:                    0
% 2.52/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.03  
% 2.52/1.03  ------ Instantiation
% 2.52/1.03  
% 2.52/1.03  inst_num_of_clauses:                    316
% 2.52/1.03  inst_num_in_passive:                    81
% 2.52/1.03  inst_num_in_active:                     226
% 2.52/1.03  inst_num_in_unprocessed:                8
% 2.52/1.03  inst_num_of_loops:                      233
% 2.52/1.03  inst_num_of_learning_restarts:          0
% 2.52/1.03  inst_num_moves_active_passive:          1
% 2.52/1.03  inst_lit_activity:                      0
% 2.52/1.03  inst_lit_activity_moves:                0
% 2.52/1.03  inst_num_tautologies:                   0
% 2.52/1.03  inst_num_prop_implied:                  0
% 2.52/1.03  inst_num_existing_simplified:           0
% 2.52/1.03  inst_num_eq_res_simplified:             0
% 2.52/1.03  inst_num_child_elim:                    0
% 2.52/1.03  inst_num_of_dismatching_blockings:      64
% 2.52/1.03  inst_num_of_non_proper_insts:           430
% 2.52/1.03  inst_num_of_duplicates:                 0
% 2.52/1.03  inst_inst_num_from_inst_to_res:         0
% 2.52/1.03  inst_dismatching_checking_time:         0.
% 2.52/1.03  
% 2.52/1.03  ------ Resolution
% 2.52/1.03  
% 2.52/1.03  res_num_of_clauses:                     0
% 2.52/1.03  res_num_in_passive:                     0
% 2.52/1.03  res_num_in_active:                      0
% 2.52/1.03  res_num_of_loops:                       94
% 2.52/1.03  res_forward_subset_subsumed:            52
% 2.52/1.03  res_backward_subset_subsumed:           2
% 2.52/1.03  res_forward_subsumed:                   0
% 2.52/1.03  res_backward_subsumed:                  0
% 2.52/1.03  res_forward_subsumption_resolution:     0
% 2.52/1.03  res_backward_subsumption_resolution:    0
% 2.52/1.03  res_clause_to_clause_subsumption:       195
% 2.52/1.03  res_orphan_elimination:                 0
% 2.52/1.03  res_tautology_del:                      37
% 2.52/1.03  res_num_eq_res_simplified:              4
% 2.52/1.03  res_num_sel_changes:                    0
% 2.52/1.03  res_moves_from_active_to_pass:          0
% 2.52/1.03  
% 2.52/1.03  ------ Superposition
% 2.52/1.03  
% 2.52/1.03  sup_time_total:                         0.
% 2.52/1.03  sup_time_generating:                    0.
% 2.52/1.03  sup_time_sim_full:                      0.
% 2.52/1.03  sup_time_sim_immed:                     0.
% 2.52/1.03  
% 2.52/1.03  sup_num_of_clauses:                     52
% 2.52/1.03  sup_num_in_active:                      32
% 2.52/1.03  sup_num_in_passive:                     20
% 2.52/1.03  sup_num_of_loops:                       46
% 2.52/1.03  sup_fw_superposition:                   29
% 2.52/1.03  sup_bw_superposition:                   50
% 2.52/1.03  sup_immediate_simplified:               11
% 2.52/1.03  sup_given_eliminated:                   1
% 2.52/1.03  comparisons_done:                       0
% 2.52/1.03  comparisons_avoided:                    0
% 2.52/1.03  
% 2.52/1.03  ------ Simplifications
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  sim_fw_subset_subsumed:                 4
% 2.52/1.03  sim_bw_subset_subsumed:                 8
% 2.52/1.03  sim_fw_subsumed:                        5
% 2.52/1.03  sim_bw_subsumed:                        0
% 2.52/1.03  sim_fw_subsumption_res:                 2
% 2.52/1.03  sim_bw_subsumption_res:                 0
% 2.52/1.03  sim_tautology_del:                      2
% 2.52/1.03  sim_eq_tautology_del:                   5
% 2.52/1.03  sim_eq_res_simp:                        0
% 2.52/1.03  sim_fw_demodulated:                     1
% 2.52/1.03  sim_bw_demodulated:                     14
% 2.52/1.03  sim_light_normalised:                   1
% 2.52/1.03  sim_joinable_taut:                      0
% 2.52/1.03  sim_joinable_simp:                      0
% 2.52/1.03  sim_ac_normalised:                      0
% 2.52/1.03  sim_smt_subsumption:                    0
% 2.52/1.03  
%------------------------------------------------------------------------------
