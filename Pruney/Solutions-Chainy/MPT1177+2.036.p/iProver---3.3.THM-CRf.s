%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:54 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  178 (3640 expanded)
%              Number of clauses        :  109 ( 666 expanded)
%              Number of leaves         :   17 (1190 expanded)
%              Depth                    :   26
%              Number of atoms          :  884 (35211 expanded)
%              Number of equality atoms :  163 ( 756 expanded)
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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f31])).

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
     => ( ( ~ m1_orders_2(X2,X0,sK4)
          | ~ r2_xboole_0(X2,sK4) )
        & ( m1_orders_2(X2,X0,sK4)
          | r2_xboole_0(X2,sK4) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
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
            ( ( ~ m1_orders_2(sK3,X0,X3)
              | ~ r2_xboole_0(sK3,X3) )
            & ( m1_orders_2(sK3,X0,X3)
              | r2_xboole_0(sK3,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
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
                & m2_orders_2(X3,X0,sK2) )
            & m2_orders_2(X2,X0,sK2) )
        & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))) ) ) ),
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f44,f43,f42,f41])).

fof(f70,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f69,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

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
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(cnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f26])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1637,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1638,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
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

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_557,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_558,plain,
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
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_839,plain,
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
    inference(resolution_lifted,[status(thm)],[c_558,c_23])).

cnf(c_840,plain,
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
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_844,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_840,c_27,c_26,c_25,c_24])).

cnf(c_1085,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_844])).

cnf(c_1629,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_2654,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1629])).

cnf(c_2985,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_2654])).

cnf(c_34,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_205,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_206,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_372,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_206])).

cnf(c_373,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_374,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_382,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_206])).

cnf(c_383,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_384,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

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

cnf(c_629,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_630,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_794,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_630,c_23])).

cnf(c_795,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_799,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_27,c_26,c_25,c_24])).

cnf(c_1093,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_799])).

cnf(c_1788,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1789,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_1944,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_2135,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2136,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1943,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2156,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_2157,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

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

cnf(c_923,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_924,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_926,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_27,c_26,c_25,c_24])).

cnf(c_2389,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_2390,plain,
    ( m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2389])).

cnf(c_2994,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2985,c_34,c_35,c_374,c_384,c_1789,c_2136,c_2157,c_2390])).

cnf(c_1627,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_1632,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_1861,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1632])).

cnf(c_1992,plain,
    ( m1_orders_2(X0,sK1,sK4) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1861])).

cnf(c_2999,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2994,c_1992])).

cnf(c_1642,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3031,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2999,c_1642])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_203,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_204,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_359,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_204])).

cnf(c_360,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_361,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1785,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1786,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_1801,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_1802,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_3186,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3031,c_34,c_35,c_361,c_374,c_384,c_1786,c_1789,c_1802,c_2136,c_2157,c_2390])).

cnf(c_3191,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3186,c_2994])).

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

cnf(c_152,plain,
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

cnf(c_153,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_899,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_23])).

cnf(c_900,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_27,c_26,c_25,c_24])).

cnf(c_905,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_904])).

cnf(c_1633,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_1859,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1633])).

cnf(c_3475,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1859])).

cnf(c_3610,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3191,c_3475])).

cnf(c_3613,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3610,c_3191])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_596,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_597,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_815,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_597,c_23])).

cnf(c_816,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_820,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_27,c_26,c_25,c_24])).

cnf(c_1089,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_820])).

cnf(c_1628,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_2076,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1628])).

cnf(c_2449,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_2076])).

cnf(c_3623,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3613,c_2449])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1640,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1643,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1639,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2297,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1639])).

cnf(c_3283,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_2297])).

cnf(c_4050,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3623,c_3283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.02/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/1.01  
% 2.02/1.01  ------  iProver source info
% 2.02/1.01  
% 2.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/1.01  git: non_committed_changes: false
% 2.02/1.01  git: last_make_outside_of_git: false
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     num_symb
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       true
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  ------ Parsing...
% 2.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/1.01  ------ Proving...
% 2.02/1.01  ------ Problem Properties 
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  clauses                                 19
% 2.02/1.01  conjectures                             2
% 2.02/1.01  EPR                                     13
% 2.02/1.01  Horn                                    15
% 2.02/1.01  unary                                   4
% 2.02/1.01  binary                                  6
% 2.02/1.01  lits                                    48
% 2.02/1.01  lits eq                                 6
% 2.02/1.01  fd_pure                                 0
% 2.02/1.01  fd_pseudo                               0
% 2.02/1.01  fd_cond                                 1
% 2.02/1.01  fd_pseudo_cond                          3
% 2.02/1.01  AC symbols                              0
% 2.02/1.01  
% 2.02/1.01  ------ Schedule dynamic 5 is on 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  Current options:
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     none
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       false
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ Proving...
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS status Theorem for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01   Resolution empty clause
% 2.02/1.01  
% 2.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  fof(f12,conjecture,(
% 2.02/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f13,negated_conjecture,(
% 2.02/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.02/1.01    inference(negated_conjecture,[],[f12])).
% 2.02/1.01  
% 2.02/1.01  fof(f30,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f13])).
% 2.02/1.01  
% 2.02/1.01  fof(f31,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f30])).
% 2.02/1.01  
% 2.02/1.01  fof(f39,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f31])).
% 2.02/1.01  
% 2.02/1.01  fof(f40,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f39])).
% 2.02/1.01  
% 2.02/1.01  fof(f44,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f43,plain,(
% 2.02/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f42,plain,(
% 2.02/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f41,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f45,plain,(
% 2.02/1.01    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f44,f43,f42,f41])).
% 2.02/1.01  
% 2.02/1.01  fof(f70,plain,(
% 2.02/1.01    m2_orders_2(sK3,sK1,sK2)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f71,plain,(
% 2.02/1.01    m2_orders_2(sK4,sK1,sK2)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f11,axiom,(
% 2.02/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f28,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f11])).
% 2.02/1.01  
% 2.02/1.01  fof(f29,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f28])).
% 2.02/1.01  
% 2.02/1.01  fof(f38,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f63,plain,(
% 2.02/1.01    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f69,plain,(
% 2.02/1.01    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f68,plain,(
% 2.02/1.01    l1_orders_2(sK1)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f64,plain,(
% 2.02/1.01    ~v2_struct_0(sK1)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f65,plain,(
% 2.02/1.01    v3_orders_2(sK1)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f66,plain,(
% 2.02/1.01    v4_orders_2(sK1)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f67,plain,(
% 2.02/1.01    v5_orders_2(sK1)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f1,axiom,(
% 2.02/1.01    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f32,plain,(
% 2.02/1.01    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.02/1.01    inference(nnf_transformation,[],[f1])).
% 2.02/1.01  
% 2.02/1.01  fof(f33,plain,(
% 2.02/1.01    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.02/1.01    inference(flattening,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  fof(f46,plain,(
% 2.02/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f33])).
% 2.02/1.01  
% 2.02/1.01  fof(f72,plain,(
% 2.02/1.01    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f47,plain,(
% 2.02/1.01    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f33])).
% 2.02/1.01  
% 2.02/1.01  fof(f74,plain,(
% 2.02/1.01    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.02/1.01    inference(equality_resolution,[],[f47])).
% 2.02/1.01  
% 2.02/1.01  fof(f7,axiom,(
% 2.02/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f15,plain,(
% 2.02/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.01    inference(pure_predicate_removal,[],[f7])).
% 2.02/1.01  
% 2.02/1.01  fof(f20,plain,(
% 2.02/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f15])).
% 2.02/1.01  
% 2.02/1.01  fof(f21,plain,(
% 2.02/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f20])).
% 2.02/1.01  
% 2.02/1.01  fof(f58,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f21])).
% 2.02/1.01  
% 2.02/1.01  fof(f3,axiom,(
% 2.02/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f36,plain,(
% 2.02/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.01    inference(nnf_transformation,[],[f3])).
% 2.02/1.01  
% 2.02/1.01  fof(f37,plain,(
% 2.02/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.01    inference(flattening,[],[f36])).
% 2.02/1.01  
% 2.02/1.01  fof(f54,plain,(
% 2.02/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f37])).
% 2.02/1.01  
% 2.02/1.01  fof(f8,axiom,(
% 2.02/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f22,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f8])).
% 2.02/1.01  
% 2.02/1.01  fof(f23,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f22])).
% 2.02/1.01  
% 2.02/1.01  fof(f59,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f23])).
% 2.02/1.01  
% 2.02/1.01  fof(f48,plain,(
% 2.02/1.01    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f33])).
% 2.02/1.01  
% 2.02/1.01  fof(f73,plain,(
% 2.02/1.01    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f9,axiom,(
% 2.02/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f24,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f9])).
% 2.02/1.01  
% 2.02/1.01  fof(f25,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f24])).
% 2.02/1.01  
% 2.02/1.01  fof(f60,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f25])).
% 2.02/1.01  
% 2.02/1.01  fof(f6,axiom,(
% 2.02/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f18,plain,(
% 2.02/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f6])).
% 2.02/1.01  
% 2.02/1.01  fof(f19,plain,(
% 2.02/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f18])).
% 2.02/1.01  
% 2.02/1.01  fof(f57,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f19])).
% 2.02/1.01  
% 2.02/1.01  fof(f10,axiom,(
% 2.02/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f26,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f10])).
% 2.02/1.01  
% 2.02/1.01  fof(f27,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/1.01    inference(flattening,[],[f26])).
% 2.02/1.01  
% 2.02/1.01  fof(f61,plain,(
% 2.02/1.01    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f27])).
% 2.02/1.01  
% 2.02/1.01  fof(f4,axiom,(
% 2.02/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f55,plain,(
% 2.02/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f4])).
% 2.02/1.01  
% 2.02/1.01  fof(f2,axiom,(
% 2.02/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f14,plain,(
% 2.02/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.02/1.01    inference(rectify,[],[f2])).
% 2.02/1.01  
% 2.02/1.01  fof(f16,plain,(
% 2.02/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.02/1.01    inference(ennf_transformation,[],[f14])).
% 2.02/1.01  
% 2.02/1.01  fof(f34,plain,(
% 2.02/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f35,plain,(
% 2.02/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).
% 2.02/1.01  
% 2.02/1.01  fof(f49,plain,(
% 2.02/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f35])).
% 2.02/1.01  
% 2.02/1.01  fof(f5,axiom,(
% 2.02/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f17,plain,(
% 2.02/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.02/1.01    inference(ennf_transformation,[],[f5])).
% 2.02/1.01  
% 2.02/1.01  fof(f56,plain,(
% 2.02/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f17])).
% 2.02/1.01  
% 2.02/1.01  cnf(c_21,negated_conjecture,
% 2.02/1.01      ( m2_orders_2(sK3,sK1,sK2) ),
% 2.02/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1637,plain,
% 2.02/1.01      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_20,negated_conjecture,
% 2.02/1.01      ( m2_orders_2(sK4,sK1,sK2) ),
% 2.02/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1638,plain,
% 2.02/1.01      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_16,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.01      | m1_orders_2(X3,X1,X0)
% 2.02/1.01      | m1_orders_2(X0,X1,X3)
% 2.02/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | X3 = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_22,negated_conjecture,
% 2.02/1.01      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 2.02/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_557,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.01      | m1_orders_2(X3,X1,X0)
% 2.02/1.01      | m1_orders_2(X0,X1,X3)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | X3 = X0
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK2 != X2 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_558,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 2.02/1.01      | m1_orders_2(X0,X1,X2)
% 2.02/1.01      | m1_orders_2(X2,X1,X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | X0 = X2
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_23,negated_conjecture,
% 2.02/1.01      ( l1_orders_2(sK1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_839,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 2.02/1.01      | m1_orders_2(X0,X1,X2)
% 2.02/1.01      | m1_orders_2(X2,X1,X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | X2 = X0
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK1 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_558,c_23]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_840,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | v2_struct_0(sK1)
% 2.02/1.01      | ~ v3_orders_2(sK1)
% 2.02/1.01      | ~ v4_orders_2(sK1)
% 2.02/1.01      | ~ v5_orders_2(sK1)
% 2.02/1.01      | X1 = X0
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_839]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_27,negated_conjecture,
% 2.02/1.01      ( ~ v2_struct_0(sK1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_26,negated_conjecture,
% 2.02/1.01      ( v3_orders_2(sK1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_25,negated_conjecture,
% 2.02/1.01      ( v4_orders_2(sK1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_24,negated_conjecture,
% 2.02/1.01      ( v5_orders_2(sK1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_844,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | X1 = X0
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_840,c_27,c_26,c_25,c_24]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1085,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | X1 = X0 ),
% 2.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_844]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1629,plain,
% 2.02/1.01      ( X0 = X1
% 2.02/1.01      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.02/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_orders_2(X0,sK1,X1) = iProver_top
% 2.02/1.01      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2654,plain,
% 2.02/1.01      ( sK4 = X0
% 2.02/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 2.02/1.01      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1638,c_1629]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2985,plain,
% 2.02/1.01      ( sK4 = sK3
% 2.02/1.01      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.02/1.01      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1637,c_2654]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_34,plain,
% 2.02/1.01      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_35,plain,
% 2.02/1.01      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2,plain,
% 2.02/1.01      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_19,negated_conjecture,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_205,plain,
% 2.02/1.01      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_206,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.02/1.01      inference(renaming,[status(thm)],[c_205]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_372,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(X0,X1) | sK4 != X1 | sK3 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_206]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_373,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_372]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_374,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 2.02/1.01      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1,plain,
% 2.02/1.01      ( ~ r2_xboole_0(X0,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_382,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_206]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_383,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_382]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_384,plain,
% 2.02/1.01      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_12,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_629,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK2 != X2 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_630,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_629]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_794,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK1 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_630,c_23]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_795,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | v2_struct_0(sK1)
% 2.02/1.01      | ~ v3_orders_2(sK1)
% 2.02/1.01      | ~ v4_orders_2(sK1)
% 2.02/1.01      | ~ v5_orders_2(sK1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_794]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_799,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_795,c_27,c_26,c_25,c_24]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1093,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_799]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1788,plain,
% 2.02/1.01      ( ~ m2_orders_2(sK3,sK1,sK2)
% 2.02/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1093]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1789,plain,
% 2.02/1.01      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1944,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(sK4,sK1,sK2)
% 2.02/1.01      | m1_orders_2(X0,sK1,sK4)
% 2.02/1.01      | m1_orders_2(sK4,sK1,X0)
% 2.02/1.01      | X0 = sK4 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1085]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2135,plain,
% 2.02/1.01      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(sK3,sK1,sK2)
% 2.02/1.01      | m1_orders_2(sK4,sK1,sK3)
% 2.02/1.01      | m1_orders_2(sK3,sK1,sK4)
% 2.02/1.01      | sK3 = sK4 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1944]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2136,plain,
% 2.02/1.01      ( sK3 = sK4
% 2.02/1.01      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.02/1.01      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.02/1.01      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_6,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1943,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2156,plain,
% 2.02/1.01      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1943]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2157,plain,
% 2.02/1.01      ( sK3 = sK4
% 2.02/1.01      | r1_tarski(sK4,sK3) != iProver_top
% 2.02/1.01      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_13,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | r1_tarski(X0,X2)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_923,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | r1_tarski(X0,X2)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | sK1 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_924,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | r1_tarski(X0,X1)
% 2.02/1.01      | v2_struct_0(sK1)
% 2.02/1.01      | ~ v3_orders_2(sK1)
% 2.02/1.01      | ~ v4_orders_2(sK1)
% 2.02/1.01      | ~ v5_orders_2(sK1) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_923]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_926,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | r1_tarski(X0,X1) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_924,c_27,c_26,c_25,c_24]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2389,plain,
% 2.02/1.01      ( ~ m1_orders_2(sK4,sK1,sK3)
% 2.02/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | r1_tarski(sK4,sK3) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_926]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2390,plain,
% 2.02/1.01      ( m1_orders_2(sK4,sK1,sK3) != iProver_top
% 2.02/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.02/1.01      | r1_tarski(sK4,sK3) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_2389]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2994,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_2985,c_34,c_35,c_374,c_384,c_1789,c_2136,c_2157,c_2390]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1627,plain,
% 2.02/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1632,plain,
% 2.02/1.01      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.02/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.02/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1861,plain,
% 2.02/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.02/1.01      | r1_tarski(X1,X0) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1627,c_1632]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1992,plain,
% 2.02/1.01      ( m1_orders_2(X0,sK1,sK4) != iProver_top
% 2.02/1.01      | r1_tarski(X0,sK4) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1638,c_1861]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2999,plain,
% 2.02/1.01      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_2994,c_1992]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1642,plain,
% 2.02/1.01      ( X0 = X1
% 2.02/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.02/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3031,plain,
% 2.02/1.01      ( sK4 = sK3 | r1_tarski(sK4,sK3) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_2999,c_1642]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_0,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_18,negated_conjecture,
% 2.02/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.02/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_203,plain,
% 2.02/1.01      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_204,plain,
% 2.02/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.02/1.01      inference(renaming,[status(thm)],[c_203]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_359,plain,
% 2.02/1.01      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.02/1.01      | ~ r1_tarski(X0,X1)
% 2.02/1.01      | X1 = X0
% 2.02/1.01      | sK4 != X1
% 2.02/1.01      | sK3 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_204]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_360,plain,
% 2.02/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_359]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_361,plain,
% 2.02/1.01      ( sK4 = sK3
% 2.02/1.01      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.02/1.01      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1785,plain,
% 2.02/1.01      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.02/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1093]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1786,plain,
% 2.02/1.01      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1801,plain,
% 2.02/1.01      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.02/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | r1_tarski(sK3,sK4) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_926]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1802,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.02/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.02/1.01      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3186,plain,
% 2.02/1.01      ( sK4 = sK3 ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_3031,c_34,c_35,c_361,c_374,c_384,c_1786,c_1789,c_1802,
% 2.02/1.01                 c_2136,c_2157,c_2390]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3191,plain,
% 2.02/1.01      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 2.02/1.01      inference(demodulation,[status(thm)],[c_3186,c_2994]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_14,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_xboole_0 = X2 ),
% 2.02/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_11,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_152,plain,
% 2.02/1.01      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.01      | ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_xboole_0 = X2 ),
% 2.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_14,c_11]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_153,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_xboole_0 = X2 ),
% 2.02/1.01      inference(renaming,[status(thm)],[c_152]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_899,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m1_orders_2(X2,X1,X0)
% 2.02/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | sK1 != X1
% 2.02/1.01      | k1_xboole_0 = X2 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_153,c_23]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_900,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | v2_struct_0(sK1)
% 2.02/1.01      | ~ v3_orders_2(sK1)
% 2.02/1.01      | ~ v4_orders_2(sK1)
% 2.02/1.01      | ~ v5_orders_2(sK1)
% 2.02/1.01      | k1_xboole_0 = X0 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_899]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_904,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | k1_xboole_0 = X0 ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_900,c_27,c_26,c_25,c_24]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_905,plain,
% 2.02/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 2.02/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 2.02/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.02/1.01      | k1_xboole_0 = X1 ),
% 2.02/1.01      inference(renaming,[status(thm)],[c_904]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1633,plain,
% 2.02/1.01      ( k1_xboole_0 = X0
% 2.02/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.02/1.01      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1859,plain,
% 2.02/1.01      ( k1_xboole_0 = X0
% 2.02/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.02/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1627,c_1633]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3475,plain,
% 2.02/1.01      ( sK3 = k1_xboole_0
% 2.02/1.01      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 2.02/1.01      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1637,c_1859]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3610,plain,
% 2.02/1.01      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_3191,c_3475]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3613,plain,
% 2.02/1.01      ( sK3 = k1_xboole_0 ),
% 2.02/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3610,c_3191]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_15,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ r1_xboole_0(X0,X3)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_596,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 2.02/1.01      | ~ m2_orders_2(X3,X1,X2)
% 2.02/1.01      | ~ r1_xboole_0(X0,X3)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK2 != X2 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_597,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 2.02/1.01      | ~ r1_xboole_0(X2,X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | ~ l1_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_596]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_815,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 2.02/1.01      | ~ r1_xboole_0(X2,X0)
% 2.02/1.01      | v2_struct_0(X1)
% 2.02/1.01      | ~ v3_orders_2(X1)
% 2.02/1.01      | ~ v4_orders_2(X1)
% 2.02/1.01      | ~ v5_orders_2(X1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.02/1.01      | sK1 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_597,c_23]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_816,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | ~ r1_xboole_0(X1,X0)
% 2.02/1.01      | v2_struct_0(sK1)
% 2.02/1.01      | ~ v3_orders_2(sK1)
% 2.02/1.01      | ~ v4_orders_2(sK1)
% 2.02/1.01      | ~ v5_orders_2(sK1)
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_815]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_820,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | ~ r1_xboole_0(X1,X0)
% 2.02/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_816,c_27,c_26,c_25,c_24]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1089,plain,
% 2.02/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.02/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 2.02/1.01      | ~ r1_xboole_0(X1,X0) ),
% 2.02/1.01      inference(equality_resolution_simp,[status(thm)],[c_820]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1628,plain,
% 2.02/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.02/1.01      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2076,plain,
% 2.02/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.02/1.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1637,c_1628]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2449,plain,
% 2.02/1.01      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1637,c_2076]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3623,plain,
% 2.02/1.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.02/1.01      inference(demodulation,[status(thm)],[c_3613,c_2449]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_9,plain,
% 2.02/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1640,plain,
% 2.02/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_5,plain,
% 2.02/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1643,plain,
% 2.02/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.02/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_10,plain,
% 2.02/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1639,plain,
% 2.02/1.01      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2297,plain,
% 2.02/1.01      ( r1_xboole_0(X0,X1) = iProver_top
% 2.02/1.01      | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1643,c_1639]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3283,plain,
% 2.02/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1640,c_2297]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_4050,plain,
% 2.02/1.01      ( $false ),
% 2.02/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3623,c_3283]) ).
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  ------                               Statistics
% 2.02/1.01  
% 2.02/1.01  ------ General
% 2.02/1.01  
% 2.02/1.01  abstr_ref_over_cycles:                  0
% 2.02/1.01  abstr_ref_under_cycles:                 0
% 2.02/1.01  gc_basic_clause_elim:                   0
% 2.02/1.01  forced_gc_time:                         0
% 2.02/1.01  parsing_time:                           0.012
% 2.02/1.01  unif_index_cands_time:                  0.
% 2.02/1.01  unif_index_add_time:                    0.
% 2.02/1.01  orderings_time:                         0.
% 2.02/1.01  out_proof_time:                         0.011
% 2.02/1.01  total_time:                             0.138
% 2.02/1.01  num_of_symbols:                         53
% 2.02/1.01  num_of_terms:                           1881
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing
% 2.02/1.01  
% 2.02/1.01  num_of_splits:                          0
% 2.02/1.01  num_of_split_atoms:                     0
% 2.02/1.01  num_of_reused_defs:                     0
% 2.02/1.01  num_eq_ax_congr_red:                    19
% 2.02/1.01  num_of_sem_filtered_clauses:            1
% 2.02/1.01  num_of_subtypes:                        0
% 2.02/1.01  monotx_restored_types:                  0
% 2.02/1.01  sat_num_of_epr_types:                   0
% 2.02/1.01  sat_num_of_non_cyclic_types:            0
% 2.02/1.01  sat_guarded_non_collapsed_types:        0
% 2.02/1.01  num_pure_diseq_elim:                    0
% 2.02/1.01  simp_replaced_by:                       0
% 2.02/1.01  res_preprocessed:                       103
% 2.02/1.01  prep_upred:                             0
% 2.02/1.01  prep_unflattend:                        50
% 2.02/1.01  smt_new_axioms:                         0
% 2.02/1.01  pred_elim_cands:                        6
% 2.02/1.01  pred_elim:                              7
% 2.02/1.01  pred_elim_cl:                           8
% 2.02/1.01  pred_elim_cycles:                       11
% 2.02/1.01  merged_defs:                            2
% 2.02/1.01  merged_defs_ncl:                        0
% 2.02/1.01  bin_hyper_res:                          2
% 2.02/1.01  prep_cycles:                            4
% 2.02/1.01  pred_elim_time:                         0.015
% 2.02/1.01  splitting_time:                         0.
% 2.02/1.01  sem_filter_time:                        0.
% 2.02/1.01  monotx_time:                            0.001
% 2.02/1.01  subtype_inf_time:                       0.
% 2.02/1.01  
% 2.02/1.01  ------ Problem properties
% 2.02/1.01  
% 2.02/1.01  clauses:                                19
% 2.02/1.01  conjectures:                            2
% 2.02/1.01  epr:                                    13
% 2.02/1.01  horn:                                   15
% 2.02/1.01  ground:                                 5
% 2.02/1.01  unary:                                  4
% 2.02/1.01  binary:                                 6
% 2.02/1.01  lits:                                   48
% 2.02/1.01  lits_eq:                                6
% 2.02/1.01  fd_pure:                                0
% 2.02/1.01  fd_pseudo:                              0
% 2.02/1.01  fd_cond:                                1
% 2.02/1.01  fd_pseudo_cond:                         3
% 2.02/1.01  ac_symbols:                             0
% 2.02/1.01  
% 2.02/1.01  ------ Propositional Solver
% 2.02/1.01  
% 2.02/1.01  prop_solver_calls:                      28
% 2.02/1.01  prop_fast_solver_calls:                 937
% 2.02/1.01  smt_solver_calls:                       0
% 2.02/1.01  smt_fast_solver_calls:                  0
% 2.02/1.01  prop_num_of_clauses:                    1266
% 2.02/1.01  prop_preprocess_simplified:             4394
% 2.02/1.01  prop_fo_subsumed:                       35
% 2.02/1.01  prop_solver_time:                       0.
% 2.02/1.01  smt_solver_time:                        0.
% 2.02/1.01  smt_fast_solver_time:                   0.
% 2.02/1.01  prop_fast_solver_time:                  0.
% 2.02/1.01  prop_unsat_core_time:                   0.
% 2.02/1.01  
% 2.02/1.01  ------ QBF
% 2.02/1.01  
% 2.02/1.01  qbf_q_res:                              0
% 2.02/1.01  qbf_num_tautologies:                    0
% 2.02/1.01  qbf_prep_cycles:                        0
% 2.02/1.01  
% 2.02/1.01  ------ BMC1
% 2.02/1.01  
% 2.02/1.01  bmc1_current_bound:                     -1
% 2.02/1.01  bmc1_last_solved_bound:                 -1
% 2.02/1.01  bmc1_unsat_core_size:                   -1
% 2.02/1.01  bmc1_unsat_core_parents_size:           -1
% 2.02/1.01  bmc1_merge_next_fun:                    0
% 2.02/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation
% 2.02/1.01  
% 2.02/1.01  inst_num_of_clauses:                    356
% 2.02/1.01  inst_num_in_passive:                    6
% 2.02/1.01  inst_num_in_active:                     239
% 2.02/1.01  inst_num_in_unprocessed:                111
% 2.02/1.01  inst_num_of_loops:                      250
% 2.02/1.01  inst_num_of_learning_restarts:          0
% 2.02/1.01  inst_num_moves_active_passive:          7
% 2.02/1.01  inst_lit_activity:                      0
% 2.02/1.01  inst_lit_activity_moves:                0
% 2.02/1.01  inst_num_tautologies:                   0
% 2.02/1.01  inst_num_prop_implied:                  0
% 2.02/1.01  inst_num_existing_simplified:           0
% 2.02/1.01  inst_num_eq_res_simplified:             0
% 2.02/1.01  inst_num_child_elim:                    0
% 2.02/1.01  inst_num_of_dismatching_blockings:      11
% 2.02/1.01  inst_num_of_non_proper_insts:           347
% 2.02/1.01  inst_num_of_duplicates:                 0
% 2.02/1.01  inst_inst_num_from_inst_to_res:         0
% 2.02/1.01  inst_dismatching_checking_time:         0.
% 2.02/1.01  
% 2.02/1.01  ------ Resolution
% 2.02/1.01  
% 2.02/1.01  res_num_of_clauses:                     0
% 2.02/1.01  res_num_in_passive:                     0
% 2.02/1.01  res_num_in_active:                      0
% 2.02/1.01  res_num_of_loops:                       107
% 2.02/1.01  res_forward_subset_subsumed:            39
% 2.02/1.01  res_backward_subset_subsumed:           2
% 2.02/1.01  res_forward_subsumed:                   0
% 2.02/1.01  res_backward_subsumed:                  0
% 2.02/1.01  res_forward_subsumption_resolution:     0
% 2.02/1.01  res_backward_subsumption_resolution:    0
% 2.02/1.01  res_clause_to_clause_subsumption:       154
% 2.02/1.01  res_orphan_elimination:                 0
% 2.02/1.01  res_tautology_del:                      50
% 2.02/1.01  res_num_eq_res_simplified:              4
% 2.02/1.01  res_num_sel_changes:                    0
% 2.02/1.01  res_moves_from_active_to_pass:          0
% 2.02/1.01  
% 2.02/1.01  ------ Superposition
% 2.02/1.01  
% 2.02/1.01  sup_time_total:                         0.
% 2.02/1.01  sup_time_generating:                    0.
% 2.02/1.01  sup_time_sim_full:                      0.
% 2.02/1.01  sup_time_sim_immed:                     0.
% 2.02/1.01  
% 2.02/1.01  sup_num_of_clauses:                     42
% 2.02/1.01  sup_num_in_active:                      25
% 2.02/1.01  sup_num_in_passive:                     17
% 2.02/1.01  sup_num_of_loops:                       48
% 2.02/1.01  sup_fw_superposition:                   33
% 2.02/1.01  sup_bw_superposition:                   22
% 2.02/1.01  sup_immediate_simplified:               6
% 2.02/1.01  sup_given_eliminated:                   0
% 2.02/1.01  comparisons_done:                       0
% 2.02/1.01  comparisons_avoided:                    0
% 2.02/1.01  
% 2.02/1.01  ------ Simplifications
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  sim_fw_subset_subsumed:                 2
% 2.02/1.01  sim_bw_subset_subsumed:                 3
% 2.02/1.01  sim_fw_subsumed:                        3
% 2.02/1.01  sim_bw_subsumed:                        0
% 2.02/1.01  sim_fw_subsumption_res:                 2
% 2.02/1.01  sim_bw_subsumption_res:                 0
% 2.02/1.01  sim_tautology_del:                      1
% 2.02/1.01  sim_eq_tautology_del:                   6
% 2.02/1.01  sim_eq_res_simp:                        0
% 2.02/1.01  sim_fw_demodulated:                     1
% 2.02/1.01  sim_bw_demodulated:                     22
% 2.02/1.01  sim_light_normalised:                   2
% 2.02/1.01  sim_joinable_taut:                      0
% 2.02/1.01  sim_joinable_simp:                      0
% 2.02/1.01  sim_ac_normalised:                      0
% 2.02/1.01  sim_smt_subsumption:                    0
% 2.02/1.01  
%------------------------------------------------------------------------------
