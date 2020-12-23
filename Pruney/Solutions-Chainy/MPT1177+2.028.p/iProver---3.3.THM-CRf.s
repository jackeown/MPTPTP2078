%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:52 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  192 (4846 expanded)
%              Number of clauses        :  122 ( 834 expanded)
%              Number of leaves         :   17 (1615 expanded)
%              Depth                    :   28
%              Number of atoms          :  972 (47653 expanded)
%              Number of equality atoms :  201 ( 900 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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
     => ( ( ~ m1_orders_2(X2,X0,sK3)
          | ~ r2_xboole_0(X2,sK3) )
        & ( m1_orders_2(X2,X0,sK3)
          | r2_xboole_0(X2,sK3) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
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
            ( ( ~ m1_orders_2(sK2,X0,X3)
              | ~ r2_xboole_0(sK2,X3) )
            & ( m1_orders_2(sK2,X0,X3)
              | r2_xboole_0(sK2,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK2,X0,X1) ) ) ),
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
                & m2_orders_2(X3,X0,sK1) )
            & m2_orders_2(X2,X0,sK1) )
        & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))) ) ) ),
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42,f41,f40])).

fof(f71,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f68,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(pure_predicate_removal,[],[f8])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
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
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f24])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_212,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_213,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_430,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_213])).

cnf(c_431,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1427,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1430,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1431,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_519,plain,
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

cnf(c_520,plain,
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
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_629,plain,
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
    inference(resolution_lifted,[status(thm)],[c_520,c_23])).

cnf(c_630,plain,
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
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_634,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_27,c_26,c_25,c_24])).

cnf(c_832,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_634])).

cnf(c_1421,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1920,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1421])).

cnf(c_2157,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1920])).

cnf(c_35,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_210,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_211,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_407,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_211])).

cnf(c_408,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_409,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_558,plain,
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

cnf(c_559,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_608,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_559,c_23])).

cnf(c_609,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_27,c_26,c_25,c_24])).

cnf(c_836,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_613])).

cnf(c_1572,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_1573,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_734,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_735,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_737,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_27,c_26,c_25,c_24])).

cnf(c_1578,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1579,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_2301,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2157,c_35,c_409,c_1573,c_1579])).

cnf(c_2302,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2301])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_480,plain,
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

cnf(c_481,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m2_orders_2(X2,X1,sK1)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_659,plain,
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
    inference(resolution_lifted,[status(thm)],[c_481,c_23])).

cnf(c_660,plain,
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
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_664,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_27,c_26,c_25,c_24])).

cnf(c_828,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_664])).

cnf(c_1422,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_76,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_739,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1420,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_751,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_752,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_754,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_27,c_26,c_25,c_24])).

cnf(c_1424,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_1678,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1424])).

cnf(c_1425,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1679,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1425])).

cnf(c_2575,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_76,c_739,c_1678,c_1679])).

cnf(c_2576,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2575])).

cnf(c_2584,plain,
    ( sK2 = X0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_2576])).

cnf(c_2798,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_2584])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_420,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_213])).

cnf(c_421,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1812,plain,
    ( m1_orders_2(X0,sK0,sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1679])).

cnf(c_2307,plain,
    ( sK3 = sK2
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_1812])).

cnf(c_2308,plain,
    ( r1_tarski(sK3,sK2)
    | sK3 = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2307])).

cnf(c_1865,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2371,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_2799,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | sK3 = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2798])).

cnf(c_2829,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2798,c_421,c_2308,c_2371,c_2799])).

cnf(c_2961,plain,
    ( sK2 != sK2
    | m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1427,c_2829])).

cnf(c_2962,plain,
    ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2961])).

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
    inference(cnf_transformation,[],[f59])).

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

cnf(c_710,plain,
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

cnf(c_711,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_715,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_27,c_26,c_25,c_24])).

cnf(c_716,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_715])).

cnf(c_1426,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_1677,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1426])).

cnf(c_2894,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1677])).

cnf(c_3196,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2962,c_2894])).

cnf(c_3297,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3196,c_2962])).

cnf(c_3308,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3297,c_1430])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1433,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1432,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2031,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1433,c_1432])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1434,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2737,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1434])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

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

cnf(c_364,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_365,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_450,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_22])).

cnf(c_451,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_689,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_451,c_23])).

cnf(c_690,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_694,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_27,c_26,c_25,c_24])).

cnf(c_824,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_694])).

cnf(c_1423,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_2983,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2737,c_1423])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3308,c_2983])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.02/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.00  
% 2.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/1.00  
% 2.02/1.00  ------  iProver source info
% 2.02/1.00  
% 2.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/1.00  git: non_committed_changes: false
% 2.02/1.00  git: last_make_outside_of_git: false
% 2.02/1.00  
% 2.02/1.00  ------ 
% 2.02/1.00  
% 2.02/1.00  ------ Input Options
% 2.02/1.00  
% 2.02/1.00  --out_options                           all
% 2.02/1.00  --tptp_safe_out                         true
% 2.02/1.00  --problem_path                          ""
% 2.02/1.00  --include_path                          ""
% 2.02/1.00  --clausifier                            res/vclausify_rel
% 2.02/1.00  --clausifier_options                    --mode clausify
% 2.02/1.00  --stdin                                 false
% 2.02/1.00  --stats_out                             all
% 2.02/1.00  
% 2.02/1.00  ------ General Options
% 2.02/1.00  
% 2.02/1.00  --fof                                   false
% 2.02/1.00  --time_out_real                         305.
% 2.02/1.00  --time_out_virtual                      -1.
% 2.02/1.00  --symbol_type_check                     false
% 2.02/1.00  --clausify_out                          false
% 2.02/1.00  --sig_cnt_out                           false
% 2.02/1.00  --trig_cnt_out                          false
% 2.02/1.00  --trig_cnt_out_tolerance                1.
% 2.02/1.00  --trig_cnt_out_sk_spl                   false
% 2.02/1.00  --abstr_cl_out                          false
% 2.02/1.00  
% 2.02/1.00  ------ Global Options
% 2.02/1.00  
% 2.02/1.00  --schedule                              default
% 2.02/1.00  --add_important_lit                     false
% 2.02/1.00  --prop_solver_per_cl                    1000
% 2.02/1.00  --min_unsat_core                        false
% 2.02/1.00  --soft_assumptions                      false
% 2.02/1.00  --soft_lemma_size                       3
% 2.02/1.00  --prop_impl_unit_size                   0
% 2.02/1.00  --prop_impl_unit                        []
% 2.02/1.00  --share_sel_clauses                     true
% 2.02/1.00  --reset_solvers                         false
% 2.02/1.00  --bc_imp_inh                            [conj_cone]
% 2.02/1.00  --conj_cone_tolerance                   3.
% 2.02/1.00  --extra_neg_conj                        none
% 2.02/1.00  --large_theory_mode                     true
% 2.02/1.00  --prolific_symb_bound                   200
% 2.02/1.00  --lt_threshold                          2000
% 2.02/1.00  --clause_weak_htbl                      true
% 2.02/1.00  --gc_record_bc_elim                     false
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing Options
% 2.02/1.00  
% 2.02/1.00  --preprocessing_flag                    true
% 2.02/1.00  --time_out_prep_mult                    0.1
% 2.02/1.00  --splitting_mode                        input
% 2.02/1.00  --splitting_grd                         true
% 2.02/1.00  --splitting_cvd                         false
% 2.02/1.00  --splitting_cvd_svl                     false
% 2.02/1.00  --splitting_nvd                         32
% 2.02/1.00  --sub_typing                            true
% 2.02/1.00  --prep_gs_sim                           true
% 2.02/1.00  --prep_unflatten                        true
% 2.02/1.00  --prep_res_sim                          true
% 2.02/1.00  --prep_upred                            true
% 2.02/1.00  --prep_sem_filter                       exhaustive
% 2.02/1.00  --prep_sem_filter_out                   false
% 2.02/1.00  --pred_elim                             true
% 2.02/1.00  --res_sim_input                         true
% 2.02/1.00  --eq_ax_congr_red                       true
% 2.02/1.00  --pure_diseq_elim                       true
% 2.02/1.00  --brand_transform                       false
% 2.02/1.00  --non_eq_to_eq                          false
% 2.02/1.00  --prep_def_merge                        true
% 2.02/1.00  --prep_def_merge_prop_impl              false
% 2.02/1.00  --prep_def_merge_mbd                    true
% 2.02/1.00  --prep_def_merge_tr_red                 false
% 2.02/1.00  --prep_def_merge_tr_cl                  false
% 2.02/1.00  --smt_preprocessing                     true
% 2.02/1.00  --smt_ac_axioms                         fast
% 2.02/1.00  --preprocessed_out                      false
% 2.02/1.00  --preprocessed_stats                    false
% 2.02/1.00  
% 2.02/1.00  ------ Abstraction refinement Options
% 2.02/1.00  
% 2.02/1.00  --abstr_ref                             []
% 2.02/1.00  --abstr_ref_prep                        false
% 2.02/1.00  --abstr_ref_until_sat                   false
% 2.02/1.00  --abstr_ref_sig_restrict                funpre
% 2.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.00  --abstr_ref_under                       []
% 2.02/1.00  
% 2.02/1.00  ------ SAT Options
% 2.02/1.00  
% 2.02/1.00  --sat_mode                              false
% 2.02/1.00  --sat_fm_restart_options                ""
% 2.02/1.00  --sat_gr_def                            false
% 2.02/1.00  --sat_epr_types                         true
% 2.02/1.00  --sat_non_cyclic_types                  false
% 2.02/1.00  --sat_finite_models                     false
% 2.02/1.00  --sat_fm_lemmas                         false
% 2.02/1.00  --sat_fm_prep                           false
% 2.02/1.00  --sat_fm_uc_incr                        true
% 2.02/1.00  --sat_out_model                         small
% 2.02/1.00  --sat_out_clauses                       false
% 2.02/1.00  
% 2.02/1.00  ------ QBF Options
% 2.02/1.00  
% 2.02/1.00  --qbf_mode                              false
% 2.02/1.00  --qbf_elim_univ                         false
% 2.02/1.00  --qbf_dom_inst                          none
% 2.02/1.00  --qbf_dom_pre_inst                      false
% 2.02/1.00  --qbf_sk_in                             false
% 2.02/1.00  --qbf_pred_elim                         true
% 2.02/1.00  --qbf_split                             512
% 2.02/1.00  
% 2.02/1.00  ------ BMC1 Options
% 2.02/1.00  
% 2.02/1.00  --bmc1_incremental                      false
% 2.02/1.00  --bmc1_axioms                           reachable_all
% 2.02/1.00  --bmc1_min_bound                        0
% 2.02/1.00  --bmc1_max_bound                        -1
% 2.02/1.00  --bmc1_max_bound_default                -1
% 2.02/1.00  --bmc1_symbol_reachability              true
% 2.02/1.00  --bmc1_property_lemmas                  false
% 2.02/1.00  --bmc1_k_induction                      false
% 2.02/1.00  --bmc1_non_equiv_states                 false
% 2.02/1.00  --bmc1_deadlock                         false
% 2.02/1.00  --bmc1_ucm                              false
% 2.02/1.00  --bmc1_add_unsat_core                   none
% 2.02/1.00  --bmc1_unsat_core_children              false
% 2.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.00  --bmc1_out_stat                         full
% 2.02/1.00  --bmc1_ground_init                      false
% 2.02/1.00  --bmc1_pre_inst_next_state              false
% 2.02/1.00  --bmc1_pre_inst_state                   false
% 2.02/1.00  --bmc1_pre_inst_reach_state             false
% 2.02/1.00  --bmc1_out_unsat_core                   false
% 2.02/1.00  --bmc1_aig_witness_out                  false
% 2.02/1.00  --bmc1_verbose                          false
% 2.02/1.00  --bmc1_dump_clauses_tptp                false
% 2.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.00  --bmc1_dump_file                        -
% 2.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.00  --bmc1_ucm_extend_mode                  1
% 2.02/1.00  --bmc1_ucm_init_mode                    2
% 2.02/1.00  --bmc1_ucm_cone_mode                    none
% 2.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.00  --bmc1_ucm_relax_model                  4
% 2.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.00  --bmc1_ucm_layered_model                none
% 2.02/1.00  --bmc1_ucm_max_lemma_size               10
% 2.02/1.00  
% 2.02/1.00  ------ AIG Options
% 2.02/1.00  
% 2.02/1.00  --aig_mode                              false
% 2.02/1.00  
% 2.02/1.00  ------ Instantiation Options
% 2.02/1.00  
% 2.02/1.00  --instantiation_flag                    true
% 2.02/1.00  --inst_sos_flag                         false
% 2.02/1.00  --inst_sos_phase                        true
% 2.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.00  --inst_lit_sel_side                     num_symb
% 2.02/1.00  --inst_solver_per_active                1400
% 2.02/1.00  --inst_solver_calls_frac                1.
% 2.02/1.00  --inst_passive_queue_type               priority_queues
% 2.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.00  --inst_passive_queues_freq              [25;2]
% 2.02/1.00  --inst_dismatching                      true
% 2.02/1.00  --inst_eager_unprocessed_to_passive     true
% 2.02/1.00  --inst_prop_sim_given                   true
% 2.02/1.00  --inst_prop_sim_new                     false
% 2.02/1.00  --inst_subs_new                         false
% 2.02/1.00  --inst_eq_res_simp                      false
% 2.02/1.00  --inst_subs_given                       false
% 2.02/1.00  --inst_orphan_elimination               true
% 2.02/1.00  --inst_learning_loop_flag               true
% 2.02/1.00  --inst_learning_start                   3000
% 2.02/1.00  --inst_learning_factor                  2
% 2.02/1.00  --inst_start_prop_sim_after_learn       3
% 2.02/1.00  --inst_sel_renew                        solver
% 2.02/1.00  --inst_lit_activity_flag                true
% 2.02/1.00  --inst_restr_to_given                   false
% 2.02/1.00  --inst_activity_threshold               500
% 2.02/1.00  --inst_out_proof                        true
% 2.02/1.00  
% 2.02/1.00  ------ Resolution Options
% 2.02/1.00  
% 2.02/1.00  --resolution_flag                       true
% 2.02/1.00  --res_lit_sel                           adaptive
% 2.02/1.00  --res_lit_sel_side                      none
% 2.02/1.00  --res_ordering                          kbo
% 2.02/1.00  --res_to_prop_solver                    active
% 2.02/1.00  --res_prop_simpl_new                    false
% 2.02/1.00  --res_prop_simpl_given                  true
% 2.02/1.00  --res_passive_queue_type                priority_queues
% 2.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.00  --res_passive_queues_freq               [15;5]
% 2.02/1.00  --res_forward_subs                      full
% 2.02/1.00  --res_backward_subs                     full
% 2.02/1.00  --res_forward_subs_resolution           true
% 2.02/1.00  --res_backward_subs_resolution          true
% 2.02/1.00  --res_orphan_elimination                true
% 2.02/1.00  --res_time_limit                        2.
% 2.02/1.00  --res_out_proof                         true
% 2.02/1.00  
% 2.02/1.00  ------ Superposition Options
% 2.02/1.00  
% 2.02/1.00  --superposition_flag                    true
% 2.02/1.00  --sup_passive_queue_type                priority_queues
% 2.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.00  --demod_completeness_check              fast
% 2.02/1.00  --demod_use_ground                      true
% 2.02/1.00  --sup_to_prop_solver                    passive
% 2.02/1.00  --sup_prop_simpl_new                    true
% 2.02/1.00  --sup_prop_simpl_given                  true
% 2.02/1.00  --sup_fun_splitting                     false
% 2.02/1.00  --sup_smt_interval                      50000
% 2.02/1.00  
% 2.02/1.00  ------ Superposition Simplification Setup
% 2.02/1.00  
% 2.02/1.00  --sup_indices_passive                   []
% 2.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_full_bw                           [BwDemod]
% 2.02/1.00  --sup_immed_triv                        [TrivRules]
% 2.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_immed_bw_main                     []
% 2.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.00  
% 2.02/1.00  ------ Combination Options
% 2.02/1.00  
% 2.02/1.00  --comb_res_mult                         3
% 2.02/1.00  --comb_sup_mult                         2
% 2.02/1.00  --comb_inst_mult                        10
% 2.02/1.00  
% 2.02/1.00  ------ Debug Options
% 2.02/1.00  
% 2.02/1.00  --dbg_backtrace                         false
% 2.02/1.00  --dbg_dump_prop_clauses                 false
% 2.02/1.00  --dbg_dump_prop_clauses_file            -
% 2.02/1.00  --dbg_out_stat                          false
% 2.02/1.00  ------ Parsing...
% 2.02/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/1.00  ------ Proving...
% 2.02/1.00  ------ Problem Properties 
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  clauses                                 18
% 2.02/1.00  conjectures                             2
% 2.02/1.00  EPR                                     10
% 2.02/1.00  Horn                                    16
% 2.02/1.00  unary                                   4
% 2.02/1.00  binary                                  7
% 2.02/1.00  lits                                    44
% 2.02/1.00  lits eq                                 9
% 2.02/1.00  fd_pure                                 0
% 2.02/1.00  fd_pseudo                               0
% 2.02/1.00  fd_cond                                 2
% 2.02/1.00  fd_pseudo_cond                          3
% 2.02/1.00  AC symbols                              0
% 2.02/1.00  
% 2.02/1.00  ------ Schedule dynamic 5 is on 
% 2.02/1.00  
% 2.02/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  ------ 
% 2.02/1.00  Current options:
% 2.02/1.00  ------ 
% 2.02/1.00  
% 2.02/1.00  ------ Input Options
% 2.02/1.00  
% 2.02/1.00  --out_options                           all
% 2.02/1.00  --tptp_safe_out                         true
% 2.02/1.00  --problem_path                          ""
% 2.02/1.00  --include_path                          ""
% 2.02/1.00  --clausifier                            res/vclausify_rel
% 2.02/1.00  --clausifier_options                    --mode clausify
% 2.02/1.00  --stdin                                 false
% 2.02/1.00  --stats_out                             all
% 2.02/1.00  
% 2.02/1.00  ------ General Options
% 2.02/1.00  
% 2.02/1.00  --fof                                   false
% 2.02/1.00  --time_out_real                         305.
% 2.02/1.00  --time_out_virtual                      -1.
% 2.02/1.00  --symbol_type_check                     false
% 2.02/1.00  --clausify_out                          false
% 2.02/1.00  --sig_cnt_out                           false
% 2.02/1.00  --trig_cnt_out                          false
% 2.02/1.00  --trig_cnt_out_tolerance                1.
% 2.02/1.00  --trig_cnt_out_sk_spl                   false
% 2.02/1.00  --abstr_cl_out                          false
% 2.02/1.00  
% 2.02/1.00  ------ Global Options
% 2.02/1.00  
% 2.02/1.00  --schedule                              default
% 2.02/1.00  --add_important_lit                     false
% 2.02/1.00  --prop_solver_per_cl                    1000
% 2.02/1.00  --min_unsat_core                        false
% 2.02/1.00  --soft_assumptions                      false
% 2.02/1.00  --soft_lemma_size                       3
% 2.02/1.00  --prop_impl_unit_size                   0
% 2.02/1.00  --prop_impl_unit                        []
% 2.02/1.00  --share_sel_clauses                     true
% 2.02/1.00  --reset_solvers                         false
% 2.02/1.00  --bc_imp_inh                            [conj_cone]
% 2.02/1.00  --conj_cone_tolerance                   3.
% 2.02/1.00  --extra_neg_conj                        none
% 2.02/1.00  --large_theory_mode                     true
% 2.02/1.00  --prolific_symb_bound                   200
% 2.02/1.00  --lt_threshold                          2000
% 2.02/1.00  --clause_weak_htbl                      true
% 2.02/1.00  --gc_record_bc_elim                     false
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing Options
% 2.02/1.00  
% 2.02/1.00  --preprocessing_flag                    true
% 2.02/1.00  --time_out_prep_mult                    0.1
% 2.02/1.00  --splitting_mode                        input
% 2.02/1.00  --splitting_grd                         true
% 2.02/1.00  --splitting_cvd                         false
% 2.02/1.00  --splitting_cvd_svl                     false
% 2.02/1.00  --splitting_nvd                         32
% 2.02/1.00  --sub_typing                            true
% 2.02/1.00  --prep_gs_sim                           true
% 2.02/1.00  --prep_unflatten                        true
% 2.02/1.00  --prep_res_sim                          true
% 2.02/1.00  --prep_upred                            true
% 2.02/1.00  --prep_sem_filter                       exhaustive
% 2.02/1.00  --prep_sem_filter_out                   false
% 2.02/1.00  --pred_elim                             true
% 2.02/1.00  --res_sim_input                         true
% 2.02/1.00  --eq_ax_congr_red                       true
% 2.02/1.00  --pure_diseq_elim                       true
% 2.02/1.00  --brand_transform                       false
% 2.02/1.00  --non_eq_to_eq                          false
% 2.02/1.00  --prep_def_merge                        true
% 2.02/1.00  --prep_def_merge_prop_impl              false
% 2.02/1.00  --prep_def_merge_mbd                    true
% 2.02/1.00  --prep_def_merge_tr_red                 false
% 2.02/1.00  --prep_def_merge_tr_cl                  false
% 2.02/1.00  --smt_preprocessing                     true
% 2.02/1.00  --smt_ac_axioms                         fast
% 2.02/1.00  --preprocessed_out                      false
% 2.02/1.00  --preprocessed_stats                    false
% 2.02/1.00  
% 2.02/1.00  ------ Abstraction refinement Options
% 2.02/1.00  
% 2.02/1.00  --abstr_ref                             []
% 2.02/1.00  --abstr_ref_prep                        false
% 2.02/1.00  --abstr_ref_until_sat                   false
% 2.02/1.00  --abstr_ref_sig_restrict                funpre
% 2.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.00  --abstr_ref_under                       []
% 2.02/1.00  
% 2.02/1.00  ------ SAT Options
% 2.02/1.00  
% 2.02/1.00  --sat_mode                              false
% 2.02/1.00  --sat_fm_restart_options                ""
% 2.02/1.00  --sat_gr_def                            false
% 2.02/1.00  --sat_epr_types                         true
% 2.02/1.00  --sat_non_cyclic_types                  false
% 2.02/1.00  --sat_finite_models                     false
% 2.02/1.00  --sat_fm_lemmas                         false
% 2.02/1.00  --sat_fm_prep                           false
% 2.02/1.00  --sat_fm_uc_incr                        true
% 2.02/1.00  --sat_out_model                         small
% 2.02/1.00  --sat_out_clauses                       false
% 2.02/1.00  
% 2.02/1.00  ------ QBF Options
% 2.02/1.00  
% 2.02/1.00  --qbf_mode                              false
% 2.02/1.00  --qbf_elim_univ                         false
% 2.02/1.00  --qbf_dom_inst                          none
% 2.02/1.00  --qbf_dom_pre_inst                      false
% 2.02/1.00  --qbf_sk_in                             false
% 2.02/1.00  --qbf_pred_elim                         true
% 2.02/1.00  --qbf_split                             512
% 2.02/1.00  
% 2.02/1.00  ------ BMC1 Options
% 2.02/1.00  
% 2.02/1.00  --bmc1_incremental                      false
% 2.02/1.00  --bmc1_axioms                           reachable_all
% 2.02/1.00  --bmc1_min_bound                        0
% 2.02/1.00  --bmc1_max_bound                        -1
% 2.02/1.00  --bmc1_max_bound_default                -1
% 2.02/1.00  --bmc1_symbol_reachability              true
% 2.02/1.00  --bmc1_property_lemmas                  false
% 2.02/1.00  --bmc1_k_induction                      false
% 2.02/1.00  --bmc1_non_equiv_states                 false
% 2.02/1.00  --bmc1_deadlock                         false
% 2.02/1.00  --bmc1_ucm                              false
% 2.02/1.00  --bmc1_add_unsat_core                   none
% 2.02/1.00  --bmc1_unsat_core_children              false
% 2.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.00  --bmc1_out_stat                         full
% 2.02/1.00  --bmc1_ground_init                      false
% 2.02/1.00  --bmc1_pre_inst_next_state              false
% 2.02/1.00  --bmc1_pre_inst_state                   false
% 2.02/1.00  --bmc1_pre_inst_reach_state             false
% 2.02/1.00  --bmc1_out_unsat_core                   false
% 2.02/1.00  --bmc1_aig_witness_out                  false
% 2.02/1.00  --bmc1_verbose                          false
% 2.02/1.00  --bmc1_dump_clauses_tptp                false
% 2.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.00  --bmc1_dump_file                        -
% 2.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.00  --bmc1_ucm_extend_mode                  1
% 2.02/1.00  --bmc1_ucm_init_mode                    2
% 2.02/1.00  --bmc1_ucm_cone_mode                    none
% 2.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.00  --bmc1_ucm_relax_model                  4
% 2.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.00  --bmc1_ucm_layered_model                none
% 2.02/1.00  --bmc1_ucm_max_lemma_size               10
% 2.02/1.00  
% 2.02/1.00  ------ AIG Options
% 2.02/1.00  
% 2.02/1.00  --aig_mode                              false
% 2.02/1.00  
% 2.02/1.00  ------ Instantiation Options
% 2.02/1.00  
% 2.02/1.00  --instantiation_flag                    true
% 2.02/1.00  --inst_sos_flag                         false
% 2.02/1.00  --inst_sos_phase                        true
% 2.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.00  --inst_lit_sel_side                     none
% 2.02/1.00  --inst_solver_per_active                1400
% 2.02/1.00  --inst_solver_calls_frac                1.
% 2.02/1.00  --inst_passive_queue_type               priority_queues
% 2.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.00  --inst_passive_queues_freq              [25;2]
% 2.02/1.00  --inst_dismatching                      true
% 2.02/1.00  --inst_eager_unprocessed_to_passive     true
% 2.02/1.00  --inst_prop_sim_given                   true
% 2.02/1.00  --inst_prop_sim_new                     false
% 2.02/1.00  --inst_subs_new                         false
% 2.02/1.00  --inst_eq_res_simp                      false
% 2.02/1.00  --inst_subs_given                       false
% 2.02/1.00  --inst_orphan_elimination               true
% 2.02/1.00  --inst_learning_loop_flag               true
% 2.02/1.00  --inst_learning_start                   3000
% 2.02/1.00  --inst_learning_factor                  2
% 2.02/1.00  --inst_start_prop_sim_after_learn       3
% 2.02/1.00  --inst_sel_renew                        solver
% 2.02/1.00  --inst_lit_activity_flag                true
% 2.02/1.00  --inst_restr_to_given                   false
% 2.02/1.00  --inst_activity_threshold               500
% 2.02/1.00  --inst_out_proof                        true
% 2.02/1.00  
% 2.02/1.00  ------ Resolution Options
% 2.02/1.00  
% 2.02/1.00  --resolution_flag                       false
% 2.02/1.00  --res_lit_sel                           adaptive
% 2.02/1.00  --res_lit_sel_side                      none
% 2.02/1.00  --res_ordering                          kbo
% 2.02/1.00  --res_to_prop_solver                    active
% 2.02/1.00  --res_prop_simpl_new                    false
% 2.02/1.00  --res_prop_simpl_given                  true
% 2.02/1.00  --res_passive_queue_type                priority_queues
% 2.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.00  --res_passive_queues_freq               [15;5]
% 2.02/1.00  --res_forward_subs                      full
% 2.02/1.00  --res_backward_subs                     full
% 2.02/1.00  --res_forward_subs_resolution           true
% 2.02/1.00  --res_backward_subs_resolution          true
% 2.02/1.00  --res_orphan_elimination                true
% 2.02/1.00  --res_time_limit                        2.
% 2.02/1.00  --res_out_proof                         true
% 2.02/1.00  
% 2.02/1.00  ------ Superposition Options
% 2.02/1.00  
% 2.02/1.00  --superposition_flag                    true
% 2.02/1.00  --sup_passive_queue_type                priority_queues
% 2.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.00  --demod_completeness_check              fast
% 2.02/1.00  --demod_use_ground                      true
% 2.02/1.00  --sup_to_prop_solver                    passive
% 2.02/1.00  --sup_prop_simpl_new                    true
% 2.02/1.00  --sup_prop_simpl_given                  true
% 2.02/1.00  --sup_fun_splitting                     false
% 2.02/1.00  --sup_smt_interval                      50000
% 2.02/1.00  
% 2.02/1.00  ------ Superposition Simplification Setup
% 2.02/1.00  
% 2.02/1.00  --sup_indices_passive                   []
% 2.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_full_bw                           [BwDemod]
% 2.02/1.00  --sup_immed_triv                        [TrivRules]
% 2.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_immed_bw_main                     []
% 2.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.00  
% 2.02/1.00  ------ Combination Options
% 2.02/1.00  
% 2.02/1.00  --comb_res_mult                         3
% 2.02/1.00  --comb_sup_mult                         2
% 2.02/1.00  --comb_inst_mult                        10
% 2.02/1.00  
% 2.02/1.00  ------ Debug Options
% 2.02/1.00  
% 2.02/1.00  --dbg_backtrace                         false
% 2.02/1.00  --dbg_dump_prop_clauses                 false
% 2.02/1.00  --dbg_dump_prop_clauses_file            -
% 2.02/1.00  --dbg_out_stat                          false
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  ------ Proving...
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  % SZS status Theorem for theBenchmark.p
% 2.02/1.00  
% 2.02/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/1.00  
% 2.02/1.00  fof(f1,axiom,(
% 2.02/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f32,plain,(
% 2.02/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.02/1.00    inference(nnf_transformation,[],[f1])).
% 2.02/1.00  
% 2.02/1.00  fof(f33,plain,(
% 2.02/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.02/1.00    inference(flattening,[],[f32])).
% 2.02/1.00  
% 2.02/1.00  fof(f46,plain,(
% 2.02/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f33])).
% 2.02/1.00  
% 2.02/1.00  fof(f73,plain,(
% 2.02/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.02/1.00    inference(equality_resolution,[],[f46])).
% 2.02/1.00  
% 2.02/1.00  fof(f13,conjecture,(
% 2.02/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f14,negated_conjecture,(
% 2.02/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.02/1.00    inference(negated_conjecture,[],[f13])).
% 2.02/1.00  
% 2.02/1.00  fof(f30,plain,(
% 2.02/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f14])).
% 2.02/1.00  
% 2.02/1.00  fof(f31,plain,(
% 2.02/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f30])).
% 2.02/1.00  
% 2.02/1.00  fof(f38,plain,(
% 2.02/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.00    inference(nnf_transformation,[],[f31])).
% 2.02/1.00  
% 2.02/1.00  fof(f39,plain,(
% 2.02/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f38])).
% 2.02/1.00  
% 2.02/1.00  fof(f43,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.02/1.00    introduced(choice_axiom,[])).
% 2.02/1.00  
% 2.02/1.00  fof(f42,plain,(
% 2.02/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.02/1.00    introduced(choice_axiom,[])).
% 2.02/1.00  
% 2.02/1.00  fof(f41,plain,(
% 2.02/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.02/1.00    introduced(choice_axiom,[])).
% 2.02/1.00  
% 2.02/1.00  fof(f40,plain,(
% 2.02/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.02/1.00    introduced(choice_axiom,[])).
% 2.02/1.00  
% 2.02/1.00  fof(f44,plain,(
% 2.02/1.00    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42,f41,f40])).
% 2.02/1.00  
% 2.02/1.00  fof(f71,plain,(
% 2.02/1.00    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f69,plain,(
% 2.02/1.00    m2_orders_2(sK2,sK0,sK1)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f70,plain,(
% 2.02/1.00    m2_orders_2(sK3,sK0,sK1)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f12,axiom,(
% 2.02/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f28,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f12])).
% 2.02/1.00  
% 2.02/1.00  fof(f29,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f28])).
% 2.02/1.00  
% 2.02/1.00  fof(f37,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(nnf_transformation,[],[f29])).
% 2.02/1.00  
% 2.02/1.00  fof(f62,plain,(
% 2.02/1.00    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f37])).
% 2.02/1.00  
% 2.02/1.00  fof(f68,plain,(
% 2.02/1.00    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f67,plain,(
% 2.02/1.00    l1_orders_2(sK0)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f63,plain,(
% 2.02/1.00    ~v2_struct_0(sK0)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f64,plain,(
% 2.02/1.00    v3_orders_2(sK0)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f65,plain,(
% 2.02/1.00    v4_orders_2(sK0)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f66,plain,(
% 2.02/1.00    v5_orders_2(sK0)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f47,plain,(
% 2.02/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f33])).
% 2.02/1.00  
% 2.02/1.00  fof(f72,plain,(
% 2.02/1.00    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.02/1.00    inference(cnf_transformation,[],[f44])).
% 2.02/1.00  
% 2.02/1.00  fof(f8,axiom,(
% 2.02/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f15,plain,(
% 2.02/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.02/1.00  
% 2.02/1.00  fof(f20,plain,(
% 2.02/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f15])).
% 2.02/1.00  
% 2.02/1.00  fof(f21,plain,(
% 2.02/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f20])).
% 2.02/1.00  
% 2.02/1.00  fof(f57,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f21])).
% 2.02/1.00  
% 2.02/1.00  fof(f9,axiom,(
% 2.02/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f22,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f9])).
% 2.02/1.00  
% 2.02/1.00  fof(f23,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f22])).
% 2.02/1.00  
% 2.02/1.00  fof(f58,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f23])).
% 2.02/1.00  
% 2.02/1.00  fof(f61,plain,(
% 2.02/1.00    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f37])).
% 2.02/1.00  
% 2.02/1.00  fof(f2,axiom,(
% 2.02/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f34,plain,(
% 2.02/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.00    inference(nnf_transformation,[],[f2])).
% 2.02/1.00  
% 2.02/1.00  fof(f35,plain,(
% 2.02/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.00    inference(flattening,[],[f34])).
% 2.02/1.00  
% 2.02/1.00  fof(f50,plain,(
% 2.02/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f35])).
% 2.02/1.00  
% 2.02/1.00  fof(f7,axiom,(
% 2.02/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f18,plain,(
% 2.02/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f7])).
% 2.02/1.00  
% 2.02/1.00  fof(f19,plain,(
% 2.02/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f18])).
% 2.02/1.00  
% 2.02/1.00  fof(f56,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f19])).
% 2.02/1.00  
% 2.02/1.00  fof(f45,plain,(
% 2.02/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f33])).
% 2.02/1.00  
% 2.02/1.00  fof(f10,axiom,(
% 2.02/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f24,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f10])).
% 2.02/1.00  
% 2.02/1.00  fof(f25,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f24])).
% 2.02/1.00  
% 2.02/1.00  fof(f59,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f25])).
% 2.02/1.00  
% 2.02/1.00  fof(f4,axiom,(
% 2.02/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f53,plain,(
% 2.02/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f4])).
% 2.02/1.00  
% 2.02/1.00  fof(f5,axiom,(
% 2.02/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f16,plain,(
% 2.02/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.02/1.00    inference(ennf_transformation,[],[f5])).
% 2.02/1.00  
% 2.02/1.00  fof(f54,plain,(
% 2.02/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f16])).
% 2.02/1.00  
% 2.02/1.00  fof(f3,axiom,(
% 2.02/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f36,plain,(
% 2.02/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.02/1.00    inference(nnf_transformation,[],[f3])).
% 2.02/1.00  
% 2.02/1.00  fof(f51,plain,(
% 2.02/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.02/1.00    inference(cnf_transformation,[],[f36])).
% 2.02/1.00  
% 2.02/1.00  fof(f6,axiom,(
% 2.02/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f17,plain,(
% 2.02/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.02/1.00    inference(ennf_transformation,[],[f6])).
% 2.02/1.00  
% 2.02/1.00  fof(f55,plain,(
% 2.02/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f17])).
% 2.02/1.00  
% 2.02/1.00  fof(f11,axiom,(
% 2.02/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 2.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.00  
% 2.02/1.00  fof(f26,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.00    inference(ennf_transformation,[],[f11])).
% 2.02/1.00  
% 2.02/1.00  fof(f27,plain,(
% 2.02/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.00    inference(flattening,[],[f26])).
% 2.02/1.00  
% 2.02/1.00  fof(f60,plain,(
% 2.02/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.00    inference(cnf_transformation,[],[f27])).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1,plain,
% 2.02/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_19,negated_conjecture,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.02/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_212,plain,
% 2.02/1.00      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.02/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_213,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_212]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_430,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_213]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_431,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1427,plain,
% 2.02/1.00      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_21,negated_conjecture,
% 2.02/1.00      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1430,plain,
% 2.02/1.00      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_20,negated_conjecture,
% 2.02/1.00      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1431,plain,
% 2.02/1.00      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_16,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.00      | m1_orders_2(X3,X1,X0)
% 2.02/1.00      | m1_orders_2(X0,X1,X3)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X3 = X0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_22,negated_conjecture,
% 2.02/1.00      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.02/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_519,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.00      | m1_orders_2(X3,X1,X0)
% 2.02/1.00      | m1_orders_2(X0,X1,X3)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X3 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK1 != X2 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_520,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 2.02/1.00      | m1_orders_2(X2,X1,X0)
% 2.02/1.00      | m1_orders_2(X0,X1,X2)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X2 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_519]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_23,negated_conjecture,
% 2.02/1.00      ( l1_orders_2(sK0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_629,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 2.02/1.00      | m1_orders_2(X0,X1,X2)
% 2.02/1.00      | m1_orders_2(X2,X1,X0)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | X2 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_520,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_630,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0)
% 2.02/1.00      | X1 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_629]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_27,negated_conjecture,
% 2.02/1.00      ( ~ v2_struct_0(sK0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_26,negated_conjecture,
% 2.02/1.00      ( v3_orders_2(sK0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_25,negated_conjecture,
% 2.02/1.00      ( v4_orders_2(sK0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_24,negated_conjecture,
% 2.02/1.00      ( v5_orders_2(sK0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_634,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | X1 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_630,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_832,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | X1 = X0 ),
% 2.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_634]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1421,plain,
% 2.02/1.00      ( X0 = X1
% 2.02/1.00      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1920,plain,
% 2.02/1.00      ( sK3 = X0
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.02/1.00      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1431,c_1421]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2157,plain,
% 2.02/1.00      ( sK3 = sK2
% 2.02/1.00      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.02/1.00      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1430,c_1920]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_35,plain,
% 2.02/1.00      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_0,plain,
% 2.02/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_18,negated_conjecture,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.02/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_210,plain,
% 2.02/1.00      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.02/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_211,plain,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_210]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_407,plain,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.02/1.00      | ~ r1_tarski(X0,X1)
% 2.02/1.00      | X1 = X0
% 2.02/1.00      | sK3 != X1
% 2.02/1.00      | sK2 != X0 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_211]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_408,plain,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_409,plain,
% 2.02/1.00      ( sK3 = sK2
% 2.02/1.00      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.02/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_12,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_558,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK1 != X2 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_559,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_608,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_559,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_609,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0)
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_608]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_613,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_609,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_836,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_613]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1572,plain,
% 2.02/1.00      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.02/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.02/1.00      inference(instantiation,[status(thm)],[c_836]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1573,plain,
% 2.02/1.00      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_13,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | r1_tarski(X0,X2)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_734,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | r1_tarski(X0,X2)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_735,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | r1_tarski(X0,X1)
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_734]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_737,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | r1_tarski(X0,X1) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_735,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1578,plain,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.02/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | r1_tarski(sK2,sK3) ),
% 2.02/1.00      inference(instantiation,[status(thm)],[c_737]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1579,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.02/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.02/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2301,plain,
% 2.02/1.00      ( m1_orders_2(sK3,sK0,sK2) = iProver_top | sK3 = sK2 ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_2157,c_35,c_409,c_1573,c_1579]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2302,plain,
% 2.02/1.00      ( sK3 = sK2 | m1_orders_2(sK3,sK0,sK2) = iProver_top ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_2301]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_17,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X3,X1,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,X1,X3)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X3 = X0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_480,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X3,X1,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,X1,X3)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X3 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK1 != X2 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_481,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X2 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_659,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ m2_orders_2(X2,X1,sK1)
% 2.02/1.00      | ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | X2 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_481,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_660,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0)
% 2.02/1.00      | X1 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_659]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_664,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | X1 = X0
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_660,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_828,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ m2_orders_2(X1,sK0,sK1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | X1 = X0 ),
% 2.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_664]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1422,plain,
% 2.02/1.00      ( X0 = X1
% 2.02/1.00      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_3,plain,
% 2.02/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_76,plain,
% 2.02/1.00      ( X0 = X1
% 2.02/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.02/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_739,plain,
% 2.02/1.00      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.02/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1420,plain,
% 2.02/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_11,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_751,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_752,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_751]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_754,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_752,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1424,plain,
% 2.02/1.00      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1678,plain,
% 2.02/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1420,c_1424]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1425,plain,
% 2.02/1.00      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.02/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1679,plain,
% 2.02/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.02/1.00      | r1_tarski(X1,X0) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1420,c_1425]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2575,plain,
% 2.02/1.00      ( X0 = X1
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_1422,c_76,c_739,c_1678,c_1679]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2576,plain,
% 2.02/1.00      ( X0 = X1
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_2575]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2584,plain,
% 2.02/1.00      ( sK2 = X0
% 2.02/1.00      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.02/1.00      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1430,c_2576]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2798,plain,
% 2.02/1.00      ( sK3 = sK2 | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_2302,c_2584]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2,plain,
% 2.02/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_420,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3)
% 2.02/1.00      | r1_tarski(X0,X1)
% 2.02/1.00      | sK3 != X1
% 2.02/1.00      | sK2 != X0 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_213]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_421,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1812,plain,
% 2.02/1.00      ( m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.02/1.00      | r1_tarski(X0,sK2) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1430,c_1679]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2307,plain,
% 2.02/1.00      ( sK3 = sK2 | r1_tarski(sK3,sK2) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_2302,c_1812]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2308,plain,
% 2.02/1.00      ( r1_tarski(sK3,sK2) | sK3 = sK2 ),
% 2.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2307]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1865,plain,
% 2.02/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.02/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2371,plain,
% 2.02/1.00      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.02/1.00      inference(instantiation,[status(thm)],[c_1865]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2799,plain,
% 2.02/1.00      ( ~ m1_orders_2(sK2,sK0,sK3) | sK3 = sK2 ),
% 2.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2798]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2829,plain,
% 2.02/1.00      ( sK3 = sK2 ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_2798,c_421,c_2308,c_2371,c_2799]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2961,plain,
% 2.02/1.00      ( sK2 != sK2 | m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 2.02/1.00      inference(light_normalisation,[status(thm)],[c_1427,c_2829]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2962,plain,
% 2.02/1.00      ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 2.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_2961]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_14,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_xboole_0 = X2 ),
% 2.02/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_154,plain,
% 2.02/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_xboole_0 = X2 ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_14,c_11]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_155,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_xboole_0 = X2 ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_154]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_710,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | sK0 != X1
% 2.02/1.00      | k1_xboole_0 = X2 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_155,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_711,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0)
% 2.02/1.00      | k1_xboole_0 = X0 ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_710]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_715,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | k1_xboole_0 = X0 ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_711,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_716,plain,
% 2.02/1.00      ( ~ m1_orders_2(X0,sK0,X1)
% 2.02/1.00      | ~ m1_orders_2(X1,sK0,X0)
% 2.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.00      | k1_xboole_0 = X1 ),
% 2.02/1.00      inference(renaming,[status(thm)],[c_715]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1426,plain,
% 2.02/1.00      ( k1_xboole_0 = X0
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1677,plain,
% 2.02/1.00      ( k1_xboole_0 = X0
% 2.02/1.00      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.02/1.00      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1420,c_1426]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2894,plain,
% 2.02/1.00      ( sK2 = k1_xboole_0
% 2.02/1.00      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.02/1.00      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1430,c_1677]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_3196,plain,
% 2.02/1.00      ( sK2 = k1_xboole_0 | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_2962,c_2894]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_3297,plain,
% 2.02/1.00      ( sK2 = k1_xboole_0 ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_3196,c_2962]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_3308,plain,
% 2.02/1.00      ( m2_orders_2(k1_xboole_0,sK0,sK1) = iProver_top ),
% 2.02/1.00      inference(demodulation,[status(thm)],[c_3297,c_1430]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_8,plain,
% 2.02/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1433,plain,
% 2.02/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_9,plain,
% 2.02/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1432,plain,
% 2.02/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2031,plain,
% 2.02/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_1433,c_1432]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_7,plain,
% 2.02/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.02/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1434,plain,
% 2.02/1.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.02/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2737,plain,
% 2.02/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_2031,c_1434]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_10,plain,
% 2.02/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.02/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_15,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1) ),
% 2.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_364,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | ~ r1_tarski(X3,X4)
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | X0 != X3
% 2.02/1.00      | k1_funct_1(X2,u1_struct_0(X1)) != X4 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_365,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_450,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK1 != X2 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_365,c_22]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_451,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | ~ l1_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_450]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_689,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,X1,sK1)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(X1)))
% 2.02/1.00      | v2_struct_0(X1)
% 2.02/1.00      | ~ v3_orders_2(X1)
% 2.02/1.00      | ~ v4_orders_2(X1)
% 2.02/1.00      | ~ v5_orders_2(X1)
% 2.02/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.02/1.00      | sK0 != X1 ),
% 2.02/1.00      inference(resolution_lifted,[status(thm)],[c_451,c_23]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_690,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
% 2.02/1.00      | v2_struct_0(sK0)
% 2.02/1.00      | ~ v3_orders_2(sK0)
% 2.02/1.00      | ~ v4_orders_2(sK0)
% 2.02/1.00      | ~ v5_orders_2(sK0)
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(unflattening,[status(thm)],[c_689]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_694,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0)))
% 2.02/1.00      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.02/1.00      inference(global_propositional_subsumption,
% 2.02/1.00                [status(thm)],
% 2.02/1.00                [c_690,c_27,c_26,c_25,c_24]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_824,plain,
% 2.02/1.00      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.02/1.00      | ~ r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
% 2.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_694]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_1423,plain,
% 2.02/1.00      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.02/1.00      | r1_tarski(X0,k1_funct_1(sK1,u1_struct_0(sK0))) != iProver_top ),
% 2.02/1.00      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(c_2983,plain,
% 2.02/1.00      ( m2_orders_2(k1_xboole_0,sK0,sK1) != iProver_top ),
% 2.02/1.00      inference(superposition,[status(thm)],[c_2737,c_1423]) ).
% 2.02/1.00  
% 2.02/1.00  cnf(contradiction,plain,
% 2.02/1.00      ( $false ),
% 2.02/1.00      inference(minisat,[status(thm)],[c_3308,c_2983]) ).
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/1.00  
% 2.02/1.00  ------                               Statistics
% 2.02/1.00  
% 2.02/1.00  ------ General
% 2.02/1.00  
% 2.02/1.00  abstr_ref_over_cycles:                  0
% 2.02/1.00  abstr_ref_under_cycles:                 0
% 2.02/1.00  gc_basic_clause_elim:                   0
% 2.02/1.00  forced_gc_time:                         0
% 2.02/1.00  parsing_time:                           0.013
% 2.02/1.00  unif_index_cands_time:                  0.
% 2.02/1.00  unif_index_add_time:                    0.
% 2.02/1.00  orderings_time:                         0.
% 2.02/1.00  out_proof_time:                         0.02
% 2.02/1.00  total_time:                             0.137
% 2.02/1.00  num_of_symbols:                         53
% 2.02/1.00  num_of_terms:                           2195
% 2.02/1.00  
% 2.02/1.00  ------ Preprocessing
% 2.02/1.00  
% 2.02/1.00  num_of_splits:                          0
% 2.02/1.00  num_of_split_atoms:                     0
% 2.02/1.00  num_of_reused_defs:                     0
% 2.02/1.00  num_eq_ax_congr_red:                    11
% 2.02/1.00  num_of_sem_filtered_clauses:            1
% 2.02/1.00  num_of_subtypes:                        0
% 2.02/1.00  monotx_restored_types:                  0
% 2.02/1.00  sat_num_of_epr_types:                   0
% 2.02/1.00  sat_num_of_non_cyclic_types:            0
% 2.02/1.00  sat_guarded_non_collapsed_types:        0
% 2.02/1.00  num_pure_diseq_elim:                    0
% 2.02/1.00  simp_replaced_by:                       0
% 2.02/1.00  res_preprocessed:                       100
% 2.02/1.00  prep_upred:                             0
% 2.02/1.00  prep_unflattend:                        20
% 2.02/1.00  smt_new_axioms:                         0
% 2.02/1.00  pred_elim_cands:                        4
% 2.02/1.00  pred_elim:                              8
% 2.02/1.00  pred_elim_cl:                           9
% 2.02/1.00  pred_elim_cycles:                       10
% 2.02/1.00  merged_defs:                            10
% 2.02/1.00  merged_defs_ncl:                        0
% 2.02/1.00  bin_hyper_res:                          10
% 2.02/1.00  prep_cycles:                            4
% 2.02/1.00  pred_elim_time:                         0.009
% 2.02/1.00  splitting_time:                         0.
% 2.02/1.00  sem_filter_time:                        0.
% 2.02/1.00  monotx_time:                            0.001
% 2.02/1.00  subtype_inf_time:                       0.
% 2.02/1.00  
% 2.02/1.00  ------ Problem properties
% 2.02/1.00  
% 2.02/1.00  clauses:                                18
% 2.02/1.00  conjectures:                            2
% 2.02/1.00  epr:                                    10
% 2.02/1.00  horn:                                   16
% 2.02/1.00  ground:                                 5
% 2.02/1.00  unary:                                  4
% 2.02/1.00  binary:                                 7
% 2.02/1.00  lits:                                   44
% 2.02/1.00  lits_eq:                                9
% 2.02/1.00  fd_pure:                                0
% 2.02/1.00  fd_pseudo:                              0
% 2.02/1.00  fd_cond:                                2
% 2.02/1.00  fd_pseudo_cond:                         3
% 2.02/1.00  ac_symbols:                             0
% 2.02/1.00  
% 2.02/1.00  ------ Propositional Solver
% 2.02/1.00  
% 2.02/1.00  prop_solver_calls:                      28
% 2.02/1.00  prop_fast_solver_calls:                 822
% 2.02/1.00  smt_solver_calls:                       0
% 2.02/1.00  smt_fast_solver_calls:                  0
% 2.02/1.00  prop_num_of_clauses:                    1026
% 2.02/1.00  prop_preprocess_simplified:             3878
% 2.02/1.00  prop_fo_subsumed:                       33
% 2.02/1.00  prop_solver_time:                       0.
% 2.02/1.00  smt_solver_time:                        0.
% 2.02/1.00  smt_fast_solver_time:                   0.
% 2.02/1.00  prop_fast_solver_time:                  0.
% 2.02/1.00  prop_unsat_core_time:                   0.
% 2.02/1.00  
% 2.02/1.00  ------ QBF
% 2.02/1.00  
% 2.02/1.00  qbf_q_res:                              0
% 2.02/1.00  qbf_num_tautologies:                    0
% 2.02/1.00  qbf_prep_cycles:                        0
% 2.02/1.00  
% 2.02/1.00  ------ BMC1
% 2.02/1.00  
% 2.02/1.00  bmc1_current_bound:                     -1
% 2.02/1.00  bmc1_last_solved_bound:                 -1
% 2.02/1.00  bmc1_unsat_core_size:                   -1
% 2.02/1.00  bmc1_unsat_core_parents_size:           -1
% 2.02/1.00  bmc1_merge_next_fun:                    0
% 2.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.02/1.00  
% 2.02/1.00  ------ Instantiation
% 2.02/1.00  
% 2.02/1.00  inst_num_of_clauses:                    284
% 2.02/1.00  inst_num_in_passive:                    37
% 2.02/1.00  inst_num_in_active:                     196
% 2.02/1.00  inst_num_in_unprocessed:                51
% 2.02/1.00  inst_num_of_loops:                      200
% 2.02/1.00  inst_num_of_learning_restarts:          0
% 2.02/1.00  inst_num_moves_active_passive:          1
% 2.02/1.00  inst_lit_activity:                      0
% 2.02/1.00  inst_lit_activity_moves:                0
% 2.02/1.00  inst_num_tautologies:                   0
% 2.02/1.00  inst_num_prop_implied:                  0
% 2.02/1.00  inst_num_existing_simplified:           0
% 2.02/1.00  inst_num_eq_res_simplified:             0
% 2.02/1.00  inst_num_child_elim:                    0
% 2.02/1.00  inst_num_of_dismatching_blockings:      51
% 2.02/1.00  inst_num_of_non_proper_insts:           270
% 2.02/1.00  inst_num_of_duplicates:                 0
% 2.02/1.00  inst_inst_num_from_inst_to_res:         0
% 2.02/1.00  inst_dismatching_checking_time:         0.
% 2.02/1.00  
% 2.02/1.00  ------ Resolution
% 2.02/1.00  
% 2.02/1.00  res_num_of_clauses:                     0
% 2.02/1.00  res_num_in_passive:                     0
% 2.02/1.00  res_num_in_active:                      0
% 2.02/1.00  res_num_of_loops:                       104
% 2.02/1.00  res_forward_subset_subsumed:            39
% 2.02/1.00  res_backward_subset_subsumed:           0
% 2.02/1.00  res_forward_subsumed:                   0
% 2.02/1.00  res_backward_subsumed:                  0
% 2.02/1.00  res_forward_subsumption_resolution:     0
% 2.02/1.00  res_backward_subsumption_resolution:    0
% 2.02/1.00  res_clause_to_clause_subsumption:       135
% 2.02/1.00  res_orphan_elimination:                 0
% 2.02/1.00  res_tautology_del:                      52
% 2.02/1.00  res_num_eq_res_simplified:              4
% 2.02/1.00  res_num_sel_changes:                    0
% 2.02/1.00  res_moves_from_active_to_pass:          0
% 2.02/1.00  
% 2.02/1.00  ------ Superposition
% 2.02/1.00  
% 2.02/1.00  sup_time_total:                         0.
% 2.02/1.00  sup_time_generating:                    0.
% 2.02/1.00  sup_time_sim_full:                      0.
% 2.02/1.00  sup_time_sim_immed:                     0.
% 2.02/1.00  
% 2.02/1.00  sup_num_of_clauses:                     32
% 2.02/1.00  sup_num_in_active:                      22
% 2.02/1.00  sup_num_in_passive:                     10
% 2.02/1.00  sup_num_of_loops:                       38
% 2.02/1.00  sup_fw_superposition:                   25
% 2.02/1.00  sup_bw_superposition:                   27
% 2.02/1.00  sup_immediate_simplified:               7
% 2.02/1.00  sup_given_eliminated:                   0
% 2.02/1.00  comparisons_done:                       0
% 2.02/1.00  comparisons_avoided:                    0
% 2.02/1.00  
% 2.02/1.00  ------ Simplifications
% 2.02/1.00  
% 2.02/1.00  
% 2.02/1.00  sim_fw_subset_subsumed:                 0
% 2.02/1.00  sim_bw_subset_subsumed:                 4
% 2.02/1.00  sim_fw_subsumed:                        6
% 2.02/1.00  sim_bw_subsumed:                        0
% 2.02/1.00  sim_fw_subsumption_res:                 2
% 2.02/1.00  sim_bw_subsumption_res:                 0
% 2.02/1.00  sim_tautology_del:                      0
% 2.02/1.00  sim_eq_tautology_del:                   6
% 2.02/1.00  sim_eq_res_simp:                        1
% 2.02/1.00  sim_fw_demodulated:                     0
% 2.02/1.00  sim_bw_demodulated:                     14
% 2.02/1.00  sim_light_normalised:                   3
% 2.02/1.00  sim_joinable_taut:                      0
% 2.02/1.00  sim_joinable_simp:                      0
% 2.02/1.00  sim_ac_normalised:                      0
% 2.02/1.00  sim_smt_subsumption:                    0
% 2.02/1.00  
%------------------------------------------------------------------------------
