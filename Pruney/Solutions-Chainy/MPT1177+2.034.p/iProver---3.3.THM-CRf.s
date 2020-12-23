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
% DateTime   : Thu Dec  3 12:12:54 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  174 (3642 expanded)
%              Number of clauses        :  110 ( 669 expanded)
%              Number of leaves         :   16 (1190 expanded)
%              Depth                    :   26
%              Number of atoms          :  849 (35200 expanded)
%              Number of equality atoms :  162 ( 765 expanded)
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

fof(f71,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
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

fof(f64,plain,(
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

fof(f70,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
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

fof(f73,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f59,plain,(
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

fof(f60,plain,(
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

fof(f74,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
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

fof(f61,plain,(
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f62,plain,(
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

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_22,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1835,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1836,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_622,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_623,plain,
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
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_954,plain,
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
    inference(resolution_lifted,[status(thm)],[c_623,c_24])).

cnf(c_955,plain,
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
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_959,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_28,c_27,c_26,c_25])).

cnf(c_1227,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_959])).

cnf(c_1827,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_2878,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1827])).

cnf(c_3240,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_2878])).

cnf(c_35,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_36,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_212,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_213,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_385,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_213])).

cnf(c_386,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_387,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_395,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_213])).

cnf(c_396,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_397,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_13,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_694,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_695,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_909,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_695,c_24])).

cnf(c_910,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_914,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_910,c_28,c_27,c_26,c_25])).

cnf(c_1235,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_914])).

cnf(c_1990,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_1991,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1990])).

cnf(c_2169,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_2388,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_2389,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2168,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2419,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_2420,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1038,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_1039,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_1038])).

cnf(c_1041,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1039,c_28,c_27,c_26,c_25])).

cnf(c_2635,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_2636,plain,
    ( m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_3249,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_35,c_36,c_387,c_397,c_1991,c_2389,c_2420,c_2636])).

cnf(c_1825,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_1830,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_2048,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1830])).

cnf(c_2149,plain,
    ( m1_orders_2(X0,sK1,sK4) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_2048])).

cnf(c_3254,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_2149])).

cnf(c_1841,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3320,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_1841])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_210,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_211,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_372,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_211])).

cnf(c_373,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_374,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_1987,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_1988,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1987])).

cnf(c_2003,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_2004,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_3614,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_35,c_36,c_374,c_387,c_397,c_1988,c_1991,c_2004,c_2389,c_2420,c_2636])).

cnf(c_3619,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3614,c_3249])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_12])).

cnf(c_159,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_1014,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_24])).

cnf(c_1015,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_1019,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_28,c_27,c_26,c_25])).

cnf(c_1020,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_1019])).

cnf(c_1831,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2046,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1831])).

cnf(c_3787,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_2046])).

cnf(c_3795,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3619,c_3787])).

cnf(c_3991,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_3619])).

cnf(c_16,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_661,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_662,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_930,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_662,c_24])).

cnf(c_931,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_935,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_28,c_27,c_26,c_25])).

cnf(c_1231,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_935])).

cnf(c_1826,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_2282,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1826])).

cnf(c_2649,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_2282])).

cnf(c_4001,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3991,c_2649])).

cnf(c_10,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1838,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1839,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3038,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1841])).

cnf(c_3449,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1838,c_3038])).

cnf(c_11,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1837,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3489,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3449,c_1837])).

cnf(c_4302,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4001,c_3489])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.81/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.01  
% 1.81/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/1.01  
% 1.81/1.01  ------  iProver source info
% 1.81/1.01  
% 1.81/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.81/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/1.01  git: non_committed_changes: false
% 1.81/1.01  git: last_make_outside_of_git: false
% 1.81/1.01  
% 1.81/1.01  ------ 
% 1.81/1.01  
% 1.81/1.01  ------ Input Options
% 1.81/1.01  
% 1.81/1.01  --out_options                           all
% 1.81/1.01  --tptp_safe_out                         true
% 1.81/1.01  --problem_path                          ""
% 1.81/1.01  --include_path                          ""
% 1.81/1.01  --clausifier                            res/vclausify_rel
% 1.81/1.01  --clausifier_options                    --mode clausify
% 1.81/1.01  --stdin                                 false
% 1.81/1.01  --stats_out                             all
% 1.81/1.01  
% 1.81/1.01  ------ General Options
% 1.81/1.01  
% 1.81/1.01  --fof                                   false
% 1.81/1.01  --time_out_real                         305.
% 1.81/1.01  --time_out_virtual                      -1.
% 1.81/1.01  --symbol_type_check                     false
% 1.81/1.01  --clausify_out                          false
% 1.81/1.01  --sig_cnt_out                           false
% 1.81/1.01  --trig_cnt_out                          false
% 1.81/1.01  --trig_cnt_out_tolerance                1.
% 1.81/1.01  --trig_cnt_out_sk_spl                   false
% 1.81/1.01  --abstr_cl_out                          false
% 1.81/1.01  
% 1.81/1.01  ------ Global Options
% 1.81/1.01  
% 1.81/1.01  --schedule                              default
% 1.81/1.01  --add_important_lit                     false
% 1.81/1.01  --prop_solver_per_cl                    1000
% 1.81/1.01  --min_unsat_core                        false
% 1.81/1.01  --soft_assumptions                      false
% 1.81/1.01  --soft_lemma_size                       3
% 1.81/1.01  --prop_impl_unit_size                   0
% 1.81/1.01  --prop_impl_unit                        []
% 1.81/1.01  --share_sel_clauses                     true
% 1.81/1.01  --reset_solvers                         false
% 1.81/1.01  --bc_imp_inh                            [conj_cone]
% 1.81/1.01  --conj_cone_tolerance                   3.
% 1.81/1.01  --extra_neg_conj                        none
% 1.81/1.01  --large_theory_mode                     true
% 1.81/1.01  --prolific_symb_bound                   200
% 1.81/1.01  --lt_threshold                          2000
% 1.81/1.01  --clause_weak_htbl                      true
% 1.81/1.01  --gc_record_bc_elim                     false
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing Options
% 1.81/1.01  
% 1.81/1.01  --preprocessing_flag                    true
% 1.81/1.01  --time_out_prep_mult                    0.1
% 1.81/1.01  --splitting_mode                        input
% 1.81/1.01  --splitting_grd                         true
% 1.81/1.01  --splitting_cvd                         false
% 1.81/1.01  --splitting_cvd_svl                     false
% 1.81/1.01  --splitting_nvd                         32
% 1.81/1.01  --sub_typing                            true
% 1.81/1.01  --prep_gs_sim                           true
% 1.81/1.01  --prep_unflatten                        true
% 1.81/1.01  --prep_res_sim                          true
% 1.81/1.01  --prep_upred                            true
% 1.81/1.01  --prep_sem_filter                       exhaustive
% 1.81/1.01  --prep_sem_filter_out                   false
% 1.81/1.01  --pred_elim                             true
% 1.81/1.01  --res_sim_input                         true
% 1.81/1.01  --eq_ax_congr_red                       true
% 1.81/1.01  --pure_diseq_elim                       true
% 1.81/1.01  --brand_transform                       false
% 1.81/1.01  --non_eq_to_eq                          false
% 1.81/1.01  --prep_def_merge                        true
% 1.81/1.01  --prep_def_merge_prop_impl              false
% 1.81/1.01  --prep_def_merge_mbd                    true
% 1.81/1.01  --prep_def_merge_tr_red                 false
% 1.81/1.01  --prep_def_merge_tr_cl                  false
% 1.81/1.01  --smt_preprocessing                     true
% 1.81/1.01  --smt_ac_axioms                         fast
% 1.81/1.01  --preprocessed_out                      false
% 1.81/1.01  --preprocessed_stats                    false
% 1.81/1.01  
% 1.81/1.01  ------ Abstraction refinement Options
% 1.81/1.01  
% 1.81/1.01  --abstr_ref                             []
% 1.81/1.01  --abstr_ref_prep                        false
% 1.81/1.01  --abstr_ref_until_sat                   false
% 1.81/1.01  --abstr_ref_sig_restrict                funpre
% 1.81/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.01  --abstr_ref_under                       []
% 1.81/1.01  
% 1.81/1.01  ------ SAT Options
% 1.81/1.01  
% 1.81/1.01  --sat_mode                              false
% 1.81/1.01  --sat_fm_restart_options                ""
% 1.81/1.01  --sat_gr_def                            false
% 1.81/1.01  --sat_epr_types                         true
% 1.81/1.01  --sat_non_cyclic_types                  false
% 1.81/1.01  --sat_finite_models                     false
% 1.81/1.01  --sat_fm_lemmas                         false
% 1.81/1.01  --sat_fm_prep                           false
% 1.81/1.01  --sat_fm_uc_incr                        true
% 1.81/1.01  --sat_out_model                         small
% 1.81/1.01  --sat_out_clauses                       false
% 1.81/1.01  
% 1.81/1.01  ------ QBF Options
% 1.81/1.01  
% 1.81/1.01  --qbf_mode                              false
% 1.81/1.01  --qbf_elim_univ                         false
% 1.81/1.01  --qbf_dom_inst                          none
% 1.81/1.01  --qbf_dom_pre_inst                      false
% 1.81/1.01  --qbf_sk_in                             false
% 1.81/1.01  --qbf_pred_elim                         true
% 1.81/1.01  --qbf_split                             512
% 1.81/1.01  
% 1.81/1.01  ------ BMC1 Options
% 1.81/1.01  
% 1.81/1.01  --bmc1_incremental                      false
% 1.81/1.01  --bmc1_axioms                           reachable_all
% 1.81/1.01  --bmc1_min_bound                        0
% 1.81/1.01  --bmc1_max_bound                        -1
% 1.81/1.01  --bmc1_max_bound_default                -1
% 1.81/1.01  --bmc1_symbol_reachability              true
% 1.81/1.01  --bmc1_property_lemmas                  false
% 1.81/1.01  --bmc1_k_induction                      false
% 1.81/1.01  --bmc1_non_equiv_states                 false
% 1.81/1.01  --bmc1_deadlock                         false
% 1.81/1.01  --bmc1_ucm                              false
% 1.81/1.01  --bmc1_add_unsat_core                   none
% 1.81/1.01  --bmc1_unsat_core_children              false
% 1.81/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.01  --bmc1_out_stat                         full
% 1.81/1.01  --bmc1_ground_init                      false
% 1.81/1.01  --bmc1_pre_inst_next_state              false
% 1.81/1.01  --bmc1_pre_inst_state                   false
% 1.81/1.01  --bmc1_pre_inst_reach_state             false
% 1.81/1.01  --bmc1_out_unsat_core                   false
% 1.81/1.01  --bmc1_aig_witness_out                  false
% 1.81/1.01  --bmc1_verbose                          false
% 1.81/1.01  --bmc1_dump_clauses_tptp                false
% 1.81/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.01  --bmc1_dump_file                        -
% 1.81/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.01  --bmc1_ucm_extend_mode                  1
% 1.81/1.01  --bmc1_ucm_init_mode                    2
% 1.81/1.01  --bmc1_ucm_cone_mode                    none
% 1.81/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.01  --bmc1_ucm_relax_model                  4
% 1.81/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.01  --bmc1_ucm_layered_model                none
% 1.81/1.01  --bmc1_ucm_max_lemma_size               10
% 1.81/1.01  
% 1.81/1.01  ------ AIG Options
% 1.81/1.01  
% 1.81/1.01  --aig_mode                              false
% 1.81/1.01  
% 1.81/1.01  ------ Instantiation Options
% 1.81/1.01  
% 1.81/1.01  --instantiation_flag                    true
% 1.81/1.01  --inst_sos_flag                         false
% 1.81/1.01  --inst_sos_phase                        true
% 1.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.01  --inst_lit_sel_side                     num_symb
% 1.81/1.01  --inst_solver_per_active                1400
% 1.81/1.01  --inst_solver_calls_frac                1.
% 1.81/1.01  --inst_passive_queue_type               priority_queues
% 1.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.01  --inst_passive_queues_freq              [25;2]
% 1.81/1.01  --inst_dismatching                      true
% 1.81/1.01  --inst_eager_unprocessed_to_passive     true
% 1.81/1.01  --inst_prop_sim_given                   true
% 1.81/1.01  --inst_prop_sim_new                     false
% 1.81/1.01  --inst_subs_new                         false
% 1.81/1.01  --inst_eq_res_simp                      false
% 1.81/1.01  --inst_subs_given                       false
% 1.81/1.01  --inst_orphan_elimination               true
% 1.81/1.01  --inst_learning_loop_flag               true
% 1.81/1.01  --inst_learning_start                   3000
% 1.81/1.01  --inst_learning_factor                  2
% 1.81/1.01  --inst_start_prop_sim_after_learn       3
% 1.81/1.01  --inst_sel_renew                        solver
% 1.81/1.01  --inst_lit_activity_flag                true
% 1.81/1.01  --inst_restr_to_given                   false
% 1.81/1.01  --inst_activity_threshold               500
% 1.81/1.01  --inst_out_proof                        true
% 1.81/1.01  
% 1.81/1.01  ------ Resolution Options
% 1.81/1.01  
% 1.81/1.01  --resolution_flag                       true
% 1.81/1.01  --res_lit_sel                           adaptive
% 1.81/1.01  --res_lit_sel_side                      none
% 1.81/1.01  --res_ordering                          kbo
% 1.81/1.01  --res_to_prop_solver                    active
% 1.81/1.01  --res_prop_simpl_new                    false
% 1.81/1.01  --res_prop_simpl_given                  true
% 1.81/1.01  --res_passive_queue_type                priority_queues
% 1.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.01  --res_passive_queues_freq               [15;5]
% 1.81/1.01  --res_forward_subs                      full
% 1.81/1.01  --res_backward_subs                     full
% 1.81/1.01  --res_forward_subs_resolution           true
% 1.81/1.01  --res_backward_subs_resolution          true
% 1.81/1.01  --res_orphan_elimination                true
% 1.81/1.01  --res_time_limit                        2.
% 1.81/1.01  --res_out_proof                         true
% 1.81/1.01  
% 1.81/1.01  ------ Superposition Options
% 1.81/1.01  
% 1.81/1.01  --superposition_flag                    true
% 1.81/1.01  --sup_passive_queue_type                priority_queues
% 1.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.01  --demod_completeness_check              fast
% 1.81/1.01  --demod_use_ground                      true
% 1.81/1.01  --sup_to_prop_solver                    passive
% 1.81/1.01  --sup_prop_simpl_new                    true
% 1.81/1.01  --sup_prop_simpl_given                  true
% 1.81/1.01  --sup_fun_splitting                     false
% 1.81/1.01  --sup_smt_interval                      50000
% 1.81/1.01  
% 1.81/1.01  ------ Superposition Simplification Setup
% 1.81/1.01  
% 1.81/1.01  --sup_indices_passive                   []
% 1.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_full_bw                           [BwDemod]
% 1.81/1.01  --sup_immed_triv                        [TrivRules]
% 1.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_immed_bw_main                     []
% 1.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.01  
% 1.81/1.01  ------ Combination Options
% 1.81/1.01  
% 1.81/1.01  --comb_res_mult                         3
% 1.81/1.01  --comb_sup_mult                         2
% 1.81/1.01  --comb_inst_mult                        10
% 1.81/1.01  
% 1.81/1.01  ------ Debug Options
% 1.81/1.01  
% 1.81/1.01  --dbg_backtrace                         false
% 1.81/1.01  --dbg_dump_prop_clauses                 false
% 1.81/1.01  --dbg_dump_prop_clauses_file            -
% 1.81/1.01  --dbg_out_stat                          false
% 1.81/1.01  ------ Parsing...
% 1.81/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/1.01  ------ Proving...
% 1.81/1.01  ------ Problem Properties 
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  clauses                                 20
% 1.81/1.01  conjectures                             2
% 1.81/1.01  EPR                                     12
% 1.81/1.01  Horn                                    16
% 1.81/1.01  unary                                   6
% 1.81/1.01  binary                                  5
% 1.81/1.01  lits                                    48
% 1.81/1.01  lits eq                                 6
% 1.81/1.01  fd_pure                                 0
% 1.81/1.01  fd_pseudo                               0
% 1.81/1.01  fd_cond                                 1
% 1.81/1.01  fd_pseudo_cond                          3
% 1.81/1.01  AC symbols                              0
% 1.81/1.01  
% 1.81/1.01  ------ Schedule dynamic 5 is on 
% 1.81/1.01  
% 1.81/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  ------ 
% 1.81/1.01  Current options:
% 1.81/1.01  ------ 
% 1.81/1.01  
% 1.81/1.01  ------ Input Options
% 1.81/1.01  
% 1.81/1.01  --out_options                           all
% 1.81/1.01  --tptp_safe_out                         true
% 1.81/1.01  --problem_path                          ""
% 1.81/1.01  --include_path                          ""
% 1.81/1.01  --clausifier                            res/vclausify_rel
% 1.81/1.01  --clausifier_options                    --mode clausify
% 1.81/1.01  --stdin                                 false
% 1.81/1.01  --stats_out                             all
% 1.81/1.01  
% 1.81/1.01  ------ General Options
% 1.81/1.01  
% 1.81/1.01  --fof                                   false
% 1.81/1.01  --time_out_real                         305.
% 1.81/1.01  --time_out_virtual                      -1.
% 1.81/1.01  --symbol_type_check                     false
% 1.81/1.01  --clausify_out                          false
% 1.81/1.01  --sig_cnt_out                           false
% 1.81/1.01  --trig_cnt_out                          false
% 1.81/1.01  --trig_cnt_out_tolerance                1.
% 1.81/1.01  --trig_cnt_out_sk_spl                   false
% 1.81/1.01  --abstr_cl_out                          false
% 1.81/1.01  
% 1.81/1.01  ------ Global Options
% 1.81/1.01  
% 1.81/1.01  --schedule                              default
% 1.81/1.01  --add_important_lit                     false
% 1.81/1.01  --prop_solver_per_cl                    1000
% 1.81/1.01  --min_unsat_core                        false
% 1.81/1.01  --soft_assumptions                      false
% 1.81/1.01  --soft_lemma_size                       3
% 1.81/1.01  --prop_impl_unit_size                   0
% 1.81/1.01  --prop_impl_unit                        []
% 1.81/1.01  --share_sel_clauses                     true
% 1.81/1.01  --reset_solvers                         false
% 1.81/1.01  --bc_imp_inh                            [conj_cone]
% 1.81/1.01  --conj_cone_tolerance                   3.
% 1.81/1.01  --extra_neg_conj                        none
% 1.81/1.01  --large_theory_mode                     true
% 1.81/1.01  --prolific_symb_bound                   200
% 1.81/1.01  --lt_threshold                          2000
% 1.81/1.01  --clause_weak_htbl                      true
% 1.81/1.01  --gc_record_bc_elim                     false
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing Options
% 1.81/1.01  
% 1.81/1.01  --preprocessing_flag                    true
% 1.81/1.01  --time_out_prep_mult                    0.1
% 1.81/1.01  --splitting_mode                        input
% 1.81/1.01  --splitting_grd                         true
% 1.81/1.01  --splitting_cvd                         false
% 1.81/1.01  --splitting_cvd_svl                     false
% 1.81/1.01  --splitting_nvd                         32
% 1.81/1.01  --sub_typing                            true
% 1.81/1.01  --prep_gs_sim                           true
% 1.81/1.01  --prep_unflatten                        true
% 1.81/1.01  --prep_res_sim                          true
% 1.81/1.01  --prep_upred                            true
% 1.81/1.01  --prep_sem_filter                       exhaustive
% 1.81/1.01  --prep_sem_filter_out                   false
% 1.81/1.01  --pred_elim                             true
% 1.81/1.01  --res_sim_input                         true
% 1.81/1.01  --eq_ax_congr_red                       true
% 1.81/1.01  --pure_diseq_elim                       true
% 1.81/1.01  --brand_transform                       false
% 1.81/1.01  --non_eq_to_eq                          false
% 1.81/1.01  --prep_def_merge                        true
% 1.81/1.01  --prep_def_merge_prop_impl              false
% 1.81/1.01  --prep_def_merge_mbd                    true
% 1.81/1.01  --prep_def_merge_tr_red                 false
% 1.81/1.01  --prep_def_merge_tr_cl                  false
% 1.81/1.01  --smt_preprocessing                     true
% 1.81/1.01  --smt_ac_axioms                         fast
% 1.81/1.01  --preprocessed_out                      false
% 1.81/1.01  --preprocessed_stats                    false
% 1.81/1.01  
% 1.81/1.01  ------ Abstraction refinement Options
% 1.81/1.01  
% 1.81/1.01  --abstr_ref                             []
% 1.81/1.01  --abstr_ref_prep                        false
% 1.81/1.01  --abstr_ref_until_sat                   false
% 1.81/1.01  --abstr_ref_sig_restrict                funpre
% 1.81/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.01  --abstr_ref_under                       []
% 1.81/1.01  
% 1.81/1.01  ------ SAT Options
% 1.81/1.01  
% 1.81/1.01  --sat_mode                              false
% 1.81/1.01  --sat_fm_restart_options                ""
% 1.81/1.01  --sat_gr_def                            false
% 1.81/1.01  --sat_epr_types                         true
% 1.81/1.01  --sat_non_cyclic_types                  false
% 1.81/1.01  --sat_finite_models                     false
% 1.81/1.01  --sat_fm_lemmas                         false
% 1.81/1.01  --sat_fm_prep                           false
% 1.81/1.01  --sat_fm_uc_incr                        true
% 1.81/1.01  --sat_out_model                         small
% 1.81/1.01  --sat_out_clauses                       false
% 1.81/1.01  
% 1.81/1.01  ------ QBF Options
% 1.81/1.01  
% 1.81/1.01  --qbf_mode                              false
% 1.81/1.01  --qbf_elim_univ                         false
% 1.81/1.01  --qbf_dom_inst                          none
% 1.81/1.01  --qbf_dom_pre_inst                      false
% 1.81/1.01  --qbf_sk_in                             false
% 1.81/1.01  --qbf_pred_elim                         true
% 1.81/1.01  --qbf_split                             512
% 1.81/1.01  
% 1.81/1.01  ------ BMC1 Options
% 1.81/1.01  
% 1.81/1.01  --bmc1_incremental                      false
% 1.81/1.01  --bmc1_axioms                           reachable_all
% 1.81/1.01  --bmc1_min_bound                        0
% 1.81/1.01  --bmc1_max_bound                        -1
% 1.81/1.01  --bmc1_max_bound_default                -1
% 1.81/1.01  --bmc1_symbol_reachability              true
% 1.81/1.01  --bmc1_property_lemmas                  false
% 1.81/1.01  --bmc1_k_induction                      false
% 1.81/1.01  --bmc1_non_equiv_states                 false
% 1.81/1.01  --bmc1_deadlock                         false
% 1.81/1.01  --bmc1_ucm                              false
% 1.81/1.01  --bmc1_add_unsat_core                   none
% 1.81/1.01  --bmc1_unsat_core_children              false
% 1.81/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.01  --bmc1_out_stat                         full
% 1.81/1.01  --bmc1_ground_init                      false
% 1.81/1.01  --bmc1_pre_inst_next_state              false
% 1.81/1.01  --bmc1_pre_inst_state                   false
% 1.81/1.01  --bmc1_pre_inst_reach_state             false
% 1.81/1.01  --bmc1_out_unsat_core                   false
% 1.81/1.01  --bmc1_aig_witness_out                  false
% 1.81/1.01  --bmc1_verbose                          false
% 1.81/1.01  --bmc1_dump_clauses_tptp                false
% 1.81/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.01  --bmc1_dump_file                        -
% 1.81/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.01  --bmc1_ucm_extend_mode                  1
% 1.81/1.01  --bmc1_ucm_init_mode                    2
% 1.81/1.01  --bmc1_ucm_cone_mode                    none
% 1.81/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.01  --bmc1_ucm_relax_model                  4
% 1.81/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.01  --bmc1_ucm_layered_model                none
% 1.81/1.01  --bmc1_ucm_max_lemma_size               10
% 1.81/1.01  
% 1.81/1.01  ------ AIG Options
% 1.81/1.01  
% 1.81/1.01  --aig_mode                              false
% 1.81/1.01  
% 1.81/1.01  ------ Instantiation Options
% 1.81/1.01  
% 1.81/1.01  --instantiation_flag                    true
% 1.81/1.01  --inst_sos_flag                         false
% 1.81/1.01  --inst_sos_phase                        true
% 1.81/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.01  --inst_lit_sel_side                     none
% 1.81/1.01  --inst_solver_per_active                1400
% 1.81/1.01  --inst_solver_calls_frac                1.
% 1.81/1.01  --inst_passive_queue_type               priority_queues
% 1.81/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.01  --inst_passive_queues_freq              [25;2]
% 1.81/1.01  --inst_dismatching                      true
% 1.81/1.01  --inst_eager_unprocessed_to_passive     true
% 1.81/1.01  --inst_prop_sim_given                   true
% 1.81/1.01  --inst_prop_sim_new                     false
% 1.81/1.01  --inst_subs_new                         false
% 1.81/1.01  --inst_eq_res_simp                      false
% 1.81/1.01  --inst_subs_given                       false
% 1.81/1.01  --inst_orphan_elimination               true
% 1.81/1.01  --inst_learning_loop_flag               true
% 1.81/1.01  --inst_learning_start                   3000
% 1.81/1.01  --inst_learning_factor                  2
% 1.81/1.01  --inst_start_prop_sim_after_learn       3
% 1.81/1.01  --inst_sel_renew                        solver
% 1.81/1.01  --inst_lit_activity_flag                true
% 1.81/1.01  --inst_restr_to_given                   false
% 1.81/1.01  --inst_activity_threshold               500
% 1.81/1.01  --inst_out_proof                        true
% 1.81/1.01  
% 1.81/1.01  ------ Resolution Options
% 1.81/1.01  
% 1.81/1.01  --resolution_flag                       false
% 1.81/1.01  --res_lit_sel                           adaptive
% 1.81/1.01  --res_lit_sel_side                      none
% 1.81/1.01  --res_ordering                          kbo
% 1.81/1.01  --res_to_prop_solver                    active
% 1.81/1.01  --res_prop_simpl_new                    false
% 1.81/1.01  --res_prop_simpl_given                  true
% 1.81/1.01  --res_passive_queue_type                priority_queues
% 1.81/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.01  --res_passive_queues_freq               [15;5]
% 1.81/1.01  --res_forward_subs                      full
% 1.81/1.01  --res_backward_subs                     full
% 1.81/1.01  --res_forward_subs_resolution           true
% 1.81/1.01  --res_backward_subs_resolution          true
% 1.81/1.01  --res_orphan_elimination                true
% 1.81/1.01  --res_time_limit                        2.
% 1.81/1.01  --res_out_proof                         true
% 1.81/1.01  
% 1.81/1.01  ------ Superposition Options
% 1.81/1.01  
% 1.81/1.01  --superposition_flag                    true
% 1.81/1.01  --sup_passive_queue_type                priority_queues
% 1.81/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.01  --demod_completeness_check              fast
% 1.81/1.01  --demod_use_ground                      true
% 1.81/1.01  --sup_to_prop_solver                    passive
% 1.81/1.01  --sup_prop_simpl_new                    true
% 1.81/1.01  --sup_prop_simpl_given                  true
% 1.81/1.01  --sup_fun_splitting                     false
% 1.81/1.01  --sup_smt_interval                      50000
% 1.81/1.01  
% 1.81/1.01  ------ Superposition Simplification Setup
% 1.81/1.01  
% 1.81/1.01  --sup_indices_passive                   []
% 1.81/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_full_bw                           [BwDemod]
% 1.81/1.01  --sup_immed_triv                        [TrivRules]
% 1.81/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_immed_bw_main                     []
% 1.81/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.01  
% 1.81/1.01  ------ Combination Options
% 1.81/1.01  
% 1.81/1.01  --comb_res_mult                         3
% 1.81/1.01  --comb_sup_mult                         2
% 1.81/1.01  --comb_inst_mult                        10
% 1.81/1.01  
% 1.81/1.01  ------ Debug Options
% 1.81/1.01  
% 1.81/1.01  --dbg_backtrace                         false
% 1.81/1.01  --dbg_dump_prop_clauses                 false
% 1.81/1.01  --dbg_dump_prop_clauses_file            -
% 1.81/1.01  --dbg_out_stat                          false
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  ------ Proving...
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  % SZS status Theorem for theBenchmark.p
% 1.81/1.01  
% 1.81/1.01   Resolution empty clause
% 1.81/1.01  
% 1.81/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/1.01  
% 1.81/1.01  fof(f13,conjecture,(
% 1.81/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f14,negated_conjecture,(
% 1.81/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.81/1.01    inference(negated_conjecture,[],[f13])).
% 1.81/1.01  
% 1.81/1.01  fof(f30,plain,(
% 1.81/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f14])).
% 1.81/1.01  
% 1.81/1.01  fof(f31,plain,(
% 1.81/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f30])).
% 1.81/1.01  
% 1.81/1.01  fof(f39,plain,(
% 1.81/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.81/1.01    inference(nnf_transformation,[],[f31])).
% 1.81/1.01  
% 1.81/1.01  fof(f40,plain,(
% 1.81/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f39])).
% 1.81/1.01  
% 1.81/1.01  fof(f44,plain,(
% 1.81/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.81/1.01    introduced(choice_axiom,[])).
% 1.81/1.01  
% 1.81/1.01  fof(f43,plain,(
% 1.81/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.81/1.01    introduced(choice_axiom,[])).
% 1.81/1.01  
% 1.81/1.01  fof(f42,plain,(
% 1.81/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.81/1.01    introduced(choice_axiom,[])).
% 1.81/1.01  
% 1.81/1.01  fof(f41,plain,(
% 1.81/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.81/1.01    introduced(choice_axiom,[])).
% 1.81/1.01  
% 1.81/1.01  fof(f45,plain,(
% 1.81/1.01    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.81/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f44,f43,f42,f41])).
% 1.81/1.01  
% 1.81/1.01  fof(f71,plain,(
% 1.81/1.01    m2_orders_2(sK3,sK1,sK2)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f72,plain,(
% 1.81/1.01    m2_orders_2(sK4,sK1,sK2)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f12,axiom,(
% 1.81/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f28,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f12])).
% 1.81/1.01  
% 1.81/1.01  fof(f29,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f28])).
% 1.81/1.01  
% 1.81/1.01  fof(f38,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(nnf_transformation,[],[f29])).
% 1.81/1.01  
% 1.81/1.01  fof(f64,plain,(
% 1.81/1.01    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f38])).
% 1.81/1.01  
% 1.81/1.01  fof(f70,plain,(
% 1.81/1.01    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f69,plain,(
% 1.81/1.01    l1_orders_2(sK1)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f65,plain,(
% 1.81/1.01    ~v2_struct_0(sK1)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f66,plain,(
% 1.81/1.01    v3_orders_2(sK1)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f67,plain,(
% 1.81/1.01    v4_orders_2(sK1)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f68,plain,(
% 1.81/1.01    v5_orders_2(sK1)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f1,axiom,(
% 1.81/1.01    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f32,plain,(
% 1.81/1.01    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.81/1.01    inference(nnf_transformation,[],[f1])).
% 1.81/1.01  
% 1.81/1.01  fof(f33,plain,(
% 1.81/1.01    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.81/1.01    inference(flattening,[],[f32])).
% 1.81/1.01  
% 1.81/1.01  fof(f46,plain,(
% 1.81/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f33])).
% 1.81/1.01  
% 1.81/1.01  fof(f73,plain,(
% 1.81/1.01    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f47,plain,(
% 1.81/1.01    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f33])).
% 1.81/1.01  
% 1.81/1.01  fof(f75,plain,(
% 1.81/1.01    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.81/1.01    inference(equality_resolution,[],[f47])).
% 1.81/1.01  
% 1.81/1.01  fof(f8,axiom,(
% 1.81/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f16,plain,(
% 1.81/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.81/1.01    inference(pure_predicate_removal,[],[f8])).
% 1.81/1.01  
% 1.81/1.01  fof(f20,plain,(
% 1.81/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f16])).
% 1.81/1.01  
% 1.81/1.01  fof(f21,plain,(
% 1.81/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f20])).
% 1.81/1.01  
% 1.81/1.01  fof(f59,plain,(
% 1.81/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f21])).
% 1.81/1.01  
% 1.81/1.01  fof(f3,axiom,(
% 1.81/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f36,plain,(
% 1.81/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/1.01    inference(nnf_transformation,[],[f3])).
% 1.81/1.01  
% 1.81/1.01  fof(f37,plain,(
% 1.81/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/1.01    inference(flattening,[],[f36])).
% 1.81/1.01  
% 1.81/1.01  fof(f54,plain,(
% 1.81/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f37])).
% 1.81/1.01  
% 1.81/1.01  fof(f9,axiom,(
% 1.81/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f22,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f9])).
% 1.81/1.01  
% 1.81/1.01  fof(f23,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f22])).
% 1.81/1.01  
% 1.81/1.01  fof(f60,plain,(
% 1.81/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f23])).
% 1.81/1.01  
% 1.81/1.01  fof(f48,plain,(
% 1.81/1.01    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f33])).
% 1.81/1.01  
% 1.81/1.01  fof(f74,plain,(
% 1.81/1.01    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.81/1.01    inference(cnf_transformation,[],[f45])).
% 1.81/1.01  
% 1.81/1.01  fof(f10,axiom,(
% 1.81/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f24,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f10])).
% 1.81/1.01  
% 1.81/1.01  fof(f25,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f24])).
% 1.81/1.01  
% 1.81/1.01  fof(f61,plain,(
% 1.81/1.01    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f25])).
% 1.81/1.01  
% 1.81/1.01  fof(f7,axiom,(
% 1.81/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f18,plain,(
% 1.81/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f7])).
% 1.81/1.01  
% 1.81/1.01  fof(f19,plain,(
% 1.81/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f18])).
% 1.81/1.01  
% 1.81/1.01  fof(f58,plain,(
% 1.81/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f19])).
% 1.81/1.01  
% 1.81/1.01  fof(f11,axiom,(
% 1.81/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f26,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.81/1.01    inference(ennf_transformation,[],[f11])).
% 1.81/1.01  
% 1.81/1.01  fof(f27,plain,(
% 1.81/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.81/1.01    inference(flattening,[],[f26])).
% 1.81/1.01  
% 1.81/1.01  fof(f62,plain,(
% 1.81/1.01    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f27])).
% 1.81/1.01  
% 1.81/1.01  fof(f5,axiom,(
% 1.81/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f56,plain,(
% 1.81/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f5])).
% 1.81/1.01  
% 1.81/1.01  fof(f4,axiom,(
% 1.81/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f55,plain,(
% 1.81/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f4])).
% 1.81/1.01  
% 1.81/1.01  fof(f6,axiom,(
% 1.81/1.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.81/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.01  
% 1.81/1.01  fof(f57,plain,(
% 1.81/1.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.81/1.01    inference(cnf_transformation,[],[f6])).
% 1.81/1.01  
% 1.81/1.01  cnf(c_22,negated_conjecture,
% 1.81/1.01      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.81/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1835,plain,
% 1.81/1.01      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_21,negated_conjecture,
% 1.81/1.01      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.81/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1836,plain,
% 1.81/1.01      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_17,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.81/1.01      | m1_orders_2(X3,X1,X0)
% 1.81/1.01      | m1_orders_2(X0,X1,X3)
% 1.81/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | X3 = X0 ),
% 1.81/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_23,negated_conjecture,
% 1.81/1.01      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 1.81/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_622,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.81/1.01      | m1_orders_2(X3,X1,X0)
% 1.81/1.01      | m1_orders_2(X0,X1,X3)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | X3 = X0
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK2 != X2 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_623,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 1.81/1.01      | m1_orders_2(X0,X1,X2)
% 1.81/1.01      | m1_orders_2(X2,X1,X0)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | X0 = X2
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_622]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_24,negated_conjecture,
% 1.81/1.01      ( l1_orders_2(sK1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_954,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 1.81/1.01      | m1_orders_2(X0,X1,X2)
% 1.81/1.01      | m1_orders_2(X2,X1,X0)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | X2 = X0
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK1 != X1 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_623,c_24]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_955,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | v2_struct_0(sK1)
% 1.81/1.01      | ~ v3_orders_2(sK1)
% 1.81/1.01      | ~ v4_orders_2(sK1)
% 1.81/1.01      | ~ v5_orders_2(sK1)
% 1.81/1.01      | X1 = X0
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_954]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_28,negated_conjecture,
% 1.81/1.01      ( ~ v2_struct_0(sK1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_27,negated_conjecture,
% 1.81/1.01      ( v3_orders_2(sK1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_26,negated_conjecture,
% 1.81/1.01      ( v4_orders_2(sK1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_25,negated_conjecture,
% 1.81/1.01      ( v5_orders_2(sK1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_959,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | X1 = X0
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_955,c_28,c_27,c_26,c_25]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1227,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | X1 = X0 ),
% 1.81/1.01      inference(equality_resolution_simp,[status(thm)],[c_959]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1827,plain,
% 1.81/1.01      ( X0 = X1
% 1.81/1.01      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 1.81/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_orders_2(X0,sK1,X1) = iProver_top
% 1.81/1.01      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2878,plain,
% 1.81/1.01      ( sK4 = X0
% 1.81/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 1.81/1.01      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1836,c_1827]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3240,plain,
% 1.81/1.01      ( sK4 = sK3
% 1.81/1.01      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.81/1.01      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1835,c_2878]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_35,plain,
% 1.81/1.01      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_36,plain,
% 1.81/1.01      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2,plain,
% 1.81/1.01      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_20,negated_conjecture,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.81/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_212,plain,
% 1.81/1.01      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 1.81/1.01      inference(prop_impl,[status(thm)],[c_20]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_213,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.81/1.01      inference(renaming,[status(thm)],[c_212]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_385,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(X0,X1) | sK4 != X1 | sK3 != X0 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_213]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_386,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_385]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_387,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.81/1.01      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1,plain,
% 1.81/1.01      ( ~ r2_xboole_0(X0,X0) ),
% 1.81/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_395,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_213]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_396,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_395]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_397,plain,
% 1.81/1.01      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_13,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_694,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK2 != X2 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_695,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_694]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_909,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK1 != X1 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_695,c_24]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_910,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | v2_struct_0(sK1)
% 1.81/1.01      | ~ v3_orders_2(sK1)
% 1.81/1.01      | ~ v4_orders_2(sK1)
% 1.81/1.01      | ~ v5_orders_2(sK1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_909]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_914,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_910,c_28,c_27,c_26,c_25]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1235,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.81/1.01      inference(equality_resolution_simp,[status(thm)],[c_914]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1990,plain,
% 1.81/1.01      ( ~ m2_orders_2(sK3,sK1,sK2)
% 1.81/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_1235]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1991,plain,
% 1.81/1.01      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1990]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2169,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.81/1.01      | m1_orders_2(X0,sK1,sK4)
% 1.81/1.01      | m1_orders_2(sK4,sK1,X0)
% 1.81/1.01      | X0 = sK4 ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_1227]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2388,plain,
% 1.81/1.01      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.81/1.01      | m1_orders_2(sK4,sK1,sK3)
% 1.81/1.01      | m1_orders_2(sK3,sK1,sK4)
% 1.81/1.01      | sK3 = sK4 ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_2169]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2389,plain,
% 1.81/1.01      ( sK3 = sK4
% 1.81/1.01      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.81/1.01      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.81/1.01      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_6,plain,
% 1.81/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.81/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2168,plain,
% 1.81/1.01      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2419,plain,
% 1.81/1.01      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_2168]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2420,plain,
% 1.81/1.01      ( sK3 = sK4
% 1.81/1.01      | r1_tarski(sK4,sK3) != iProver_top
% 1.81/1.01      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_14,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | r1_tarski(X0,X2)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1038,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | r1_tarski(X0,X2)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | sK1 != X1 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1039,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | r1_tarski(X0,X1)
% 1.81/1.01      | v2_struct_0(sK1)
% 1.81/1.01      | ~ v3_orders_2(sK1)
% 1.81/1.01      | ~ v4_orders_2(sK1)
% 1.81/1.01      | ~ v5_orders_2(sK1) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_1038]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1041,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | r1_tarski(X0,X1) ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_1039,c_28,c_27,c_26,c_25]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2635,plain,
% 1.81/1.01      ( ~ m1_orders_2(sK4,sK1,sK3)
% 1.81/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | r1_tarski(sK4,sK3) ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2636,plain,
% 1.81/1.01      ( m1_orders_2(sK4,sK1,sK3) != iProver_top
% 1.81/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.81/1.01      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3249,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_3240,c_35,c_36,c_387,c_397,c_1991,c_2389,c_2420,c_2636]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1825,plain,
% 1.81/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1830,plain,
% 1.81/1.01      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 1.81/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.81/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2048,plain,
% 1.81/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top
% 1.81/1.01      | r1_tarski(X1,X0) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1825,c_1830]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2149,plain,
% 1.81/1.01      ( m1_orders_2(X0,sK1,sK4) != iProver_top
% 1.81/1.01      | r1_tarski(X0,sK4) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1836,c_2048]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3254,plain,
% 1.81/1.01      ( r1_tarski(sK3,sK4) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_3249,c_2149]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1841,plain,
% 1.81/1.01      ( X0 = X1
% 1.81/1.01      | r1_tarski(X1,X0) != iProver_top
% 1.81/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3320,plain,
% 1.81/1.01      ( sK4 = sK3 | r1_tarski(sK4,sK3) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_3254,c_1841]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_0,plain,
% 1.81/1.01      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.81/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_19,negated_conjecture,
% 1.81/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.81/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_210,plain,
% 1.81/1.01      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 1.81/1.01      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_211,plain,
% 1.81/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.81/1.01      inference(renaming,[status(thm)],[c_210]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_372,plain,
% 1.81/1.01      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.81/1.01      | ~ r1_tarski(X0,X1)
% 1.81/1.01      | X1 = X0
% 1.81/1.01      | sK4 != X1
% 1.81/1.01      | sK3 != X0 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_211]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_373,plain,
% 1.81/1.01      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_372]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_374,plain,
% 1.81/1.01      ( sK4 = sK3
% 1.81/1.01      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.81/1.01      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1987,plain,
% 1.81/1.01      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.81/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_1235]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1988,plain,
% 1.81/1.01      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1987]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2003,plain,
% 1.81/1.01      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.81/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | r1_tarski(sK3,sK4) ),
% 1.81/1.01      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2004,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.81/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.81/1.01      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3614,plain,
% 1.81/1.01      ( sK4 = sK3 ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_3320,c_35,c_36,c_374,c_387,c_397,c_1988,c_1991,c_2004,
% 1.81/1.01                 c_2389,c_2420,c_2636]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3619,plain,
% 1.81/1.01      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 1.81/1.01      inference(demodulation,[status(thm)],[c_3614,c_3249]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_15,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_orders_2(X2,X1,X0)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_xboole_0 = X2 ),
% 1.81/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_12,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_158,plain,
% 1.81/1.01      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | ~ m1_orders_2(X2,X1,X0)
% 1.81/1.01      | ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_xboole_0 = X2 ),
% 1.81/1.01      inference(global_propositional_subsumption,[status(thm)],[c_15,c_12]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_159,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_orders_2(X2,X1,X0)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_xboole_0 = X2 ),
% 1.81/1.01      inference(renaming,[status(thm)],[c_158]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1014,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m1_orders_2(X2,X1,X0)
% 1.81/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | sK1 != X1
% 1.81/1.01      | k1_xboole_0 = X2 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_159,c_24]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1015,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | v2_struct_0(sK1)
% 1.81/1.01      | ~ v3_orders_2(sK1)
% 1.81/1.01      | ~ v4_orders_2(sK1)
% 1.81/1.01      | ~ v5_orders_2(sK1)
% 1.81/1.01      | k1_xboole_0 = X0 ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_1014]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1019,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | k1_xboole_0 = X0 ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_1015,c_28,c_27,c_26,c_25]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1020,plain,
% 1.81/1.01      ( ~ m1_orders_2(X0,sK1,X1)
% 1.81/1.01      | ~ m1_orders_2(X1,sK1,X0)
% 1.81/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.81/1.01      | k1_xboole_0 = X1 ),
% 1.81/1.01      inference(renaming,[status(thm)],[c_1019]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1831,plain,
% 1.81/1.01      ( k1_xboole_0 = X0
% 1.81/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top
% 1.81/1.01      | m1_orders_2(X0,sK1,X1) != iProver_top
% 1.81/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2046,plain,
% 1.81/1.01      ( k1_xboole_0 = X0
% 1.81/1.01      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m1_orders_2(X0,sK1,X1) != iProver_top
% 1.81/1.01      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1825,c_1831]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3787,plain,
% 1.81/1.01      ( sK3 = k1_xboole_0
% 1.81/1.01      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 1.81/1.01      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1835,c_2046]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3795,plain,
% 1.81/1.01      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_3619,c_3787]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3991,plain,
% 1.81/1.01      ( sK3 = k1_xboole_0 ),
% 1.81/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3795,c_3619]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_16,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.81/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.81/1.01      | ~ r1_xboole_0(X0,X3)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_661,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.81/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.81/1.01      | ~ r1_xboole_0(X0,X3)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK2 != X2 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_662,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 1.81/1.01      | ~ r1_xboole_0(X2,X0)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | ~ l1_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_661]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_930,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,X1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X2,X1,sK2)
% 1.81/1.01      | ~ r1_xboole_0(X2,X0)
% 1.81/1.01      | v2_struct_0(X1)
% 1.81/1.01      | ~ v3_orders_2(X1)
% 1.81/1.01      | ~ v4_orders_2(X1)
% 1.81/1.01      | ~ v5_orders_2(X1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.81/1.01      | sK1 != X1 ),
% 1.81/1.01      inference(resolution_lifted,[status(thm)],[c_662,c_24]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_931,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | ~ r1_xboole_0(X1,X0)
% 1.81/1.01      | v2_struct_0(sK1)
% 1.81/1.01      | ~ v3_orders_2(sK1)
% 1.81/1.01      | ~ v4_orders_2(sK1)
% 1.81/1.01      | ~ v5_orders_2(sK1)
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(unflattening,[status(thm)],[c_930]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_935,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | ~ r1_xboole_0(X1,X0)
% 1.81/1.01      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.81/1.01      inference(global_propositional_subsumption,
% 1.81/1.01                [status(thm)],
% 1.81/1.01                [c_931,c_28,c_27,c_26,c_25]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1231,plain,
% 1.81/1.01      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.81/1.01      | ~ m2_orders_2(X1,sK1,sK2)
% 1.81/1.01      | ~ r1_xboole_0(X1,X0) ),
% 1.81/1.01      inference(equality_resolution_simp,[status(thm)],[c_935]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1826,plain,
% 1.81/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 1.81/1.01      | r1_xboole_0(X1,X0) != iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_1231]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2282,plain,
% 1.81/1.01      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.81/1.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1835,c_1826]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_2649,plain,
% 1.81/1.01      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1835,c_2282]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_4001,plain,
% 1.81/1.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.81/1.01      inference(demodulation,[status(thm)],[c_3991,c_2649]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_10,plain,
% 1.81/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 1.81/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1838,plain,
% 1.81/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_9,plain,
% 1.81/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 1.81/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1839,plain,
% 1.81/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3038,plain,
% 1.81/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1839,c_1841]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3449,plain,
% 1.81/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_1838,c_3038]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_11,plain,
% 1.81/1.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 1.81/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_1837,plain,
% 1.81/1.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 1.81/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_3489,plain,
% 1.81/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 1.81/1.01      inference(superposition,[status(thm)],[c_3449,c_1837]) ).
% 1.81/1.01  
% 1.81/1.01  cnf(c_4302,plain,
% 1.81/1.01      ( $false ),
% 1.81/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4001,c_3489]) ).
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/1.01  
% 1.81/1.01  ------                               Statistics
% 1.81/1.01  
% 1.81/1.01  ------ General
% 1.81/1.01  
% 1.81/1.01  abstr_ref_over_cycles:                  0
% 1.81/1.01  abstr_ref_under_cycles:                 0
% 1.81/1.01  gc_basic_clause_elim:                   0
% 1.81/1.01  forced_gc_time:                         0
% 1.81/1.01  parsing_time:                           0.012
% 1.81/1.01  unif_index_cands_time:                  0.
% 1.81/1.01  unif_index_add_time:                    0.
% 1.81/1.01  orderings_time:                         0.
% 1.81/1.01  out_proof_time:                         0.013
% 1.81/1.01  total_time:                             0.173
% 1.81/1.01  num_of_symbols:                         54
% 1.81/1.01  num_of_terms:                           2349
% 1.81/1.01  
% 1.81/1.01  ------ Preprocessing
% 1.81/1.01  
% 1.81/1.01  num_of_splits:                          0
% 1.81/1.01  num_of_split_atoms:                     0
% 1.81/1.01  num_of_reused_defs:                     0
% 1.81/1.01  num_eq_ax_congr_red:                    22
% 1.81/1.01  num_of_sem_filtered_clauses:            1
% 1.81/1.01  num_of_subtypes:                        0
% 1.81/1.01  monotx_restored_types:                  0
% 1.81/1.01  sat_num_of_epr_types:                   0
% 1.81/1.01  sat_num_of_non_cyclic_types:            0
% 1.81/1.01  sat_guarded_non_collapsed_types:        0
% 1.81/1.01  num_pure_diseq_elim:                    0
% 1.81/1.01  simp_replaced_by:                       0
% 1.81/1.01  res_preprocessed:                       109
% 1.81/1.01  prep_upred:                             0
% 1.81/1.01  prep_unflattend:                        66
% 1.81/1.01  smt_new_axioms:                         0
% 1.81/1.01  pred_elim_cands:                        6
% 1.81/1.01  pred_elim:                              7
% 1.81/1.01  pred_elim_cl:                           8
% 1.81/1.01  pred_elim_cycles:                       11
% 1.81/1.01  merged_defs:                            2
% 1.81/1.01  merged_defs_ncl:                        0
% 1.81/1.01  bin_hyper_res:                          2
% 1.81/1.01  prep_cycles:                            4
% 1.81/1.01  pred_elim_time:                         0.02
% 1.81/1.01  splitting_time:                         0.
% 1.81/1.01  sem_filter_time:                        0.
% 1.81/1.01  monotx_time:                            0.
% 1.81/1.01  subtype_inf_time:                       0.
% 1.81/1.01  
% 1.81/1.01  ------ Problem properties
% 1.81/1.01  
% 1.81/1.01  clauses:                                20
% 1.81/1.01  conjectures:                            2
% 1.81/1.01  epr:                                    12
% 1.81/1.01  horn:                                   16
% 1.81/1.01  ground:                                 5
% 1.81/1.01  unary:                                  6
% 1.81/1.01  binary:                                 5
% 1.81/1.01  lits:                                   48
% 1.81/1.01  lits_eq:                                6
% 1.81/1.01  fd_pure:                                0
% 1.81/1.01  fd_pseudo:                              0
% 1.81/1.01  fd_cond:                                1
% 1.81/1.01  fd_pseudo_cond:                         3
% 1.81/1.01  ac_symbols:                             0
% 1.81/1.01  
% 1.81/1.01  ------ Propositional Solver
% 1.81/1.01  
% 1.81/1.01  prop_solver_calls:                      28
% 1.81/1.01  prop_fast_solver_calls:                 977
% 1.81/1.01  smt_solver_calls:                       0
% 1.81/1.01  smt_fast_solver_calls:                  0
% 1.81/1.01  prop_num_of_clauses:                    1314
% 1.81/1.01  prop_preprocess_simplified:             4511
% 1.81/1.01  prop_fo_subsumed:                       35
% 1.81/1.01  prop_solver_time:                       0.
% 1.81/1.01  smt_solver_time:                        0.
% 1.81/1.01  smt_fast_solver_time:                   0.
% 1.81/1.01  prop_fast_solver_time:                  0.
% 1.81/1.01  prop_unsat_core_time:                   0.
% 1.81/1.01  
% 1.81/1.01  ------ QBF
% 1.81/1.01  
% 1.81/1.01  qbf_q_res:                              0
% 1.81/1.01  qbf_num_tautologies:                    0
% 1.81/1.01  qbf_prep_cycles:                        0
% 1.81/1.01  
% 1.81/1.01  ------ BMC1
% 1.81/1.01  
% 1.81/1.01  bmc1_current_bound:                     -1
% 1.81/1.01  bmc1_last_solved_bound:                 -1
% 1.81/1.01  bmc1_unsat_core_size:                   -1
% 1.81/1.01  bmc1_unsat_core_parents_size:           -1
% 1.81/1.01  bmc1_merge_next_fun:                    0
% 1.81/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.81/1.01  
% 1.81/1.01  ------ Instantiation
% 1.81/1.01  
% 1.81/1.01  inst_num_of_clauses:                    352
% 1.81/1.01  inst_num_in_passive:                    20
% 1.81/1.01  inst_num_in_active:                     238
% 1.81/1.01  inst_num_in_unprocessed:                94
% 1.81/1.01  inst_num_of_loops:                      250
% 1.81/1.01  inst_num_of_learning_restarts:          0
% 1.81/1.01  inst_num_moves_active_passive:          7
% 1.81/1.01  inst_lit_activity:                      0
% 1.81/1.01  inst_lit_activity_moves:                0
% 1.81/1.01  inst_num_tautologies:                   0
% 1.81/1.01  inst_num_prop_implied:                  0
% 1.81/1.01  inst_num_existing_simplified:           0
% 1.81/1.01  inst_num_eq_res_simplified:             0
% 1.81/1.01  inst_num_child_elim:                    0
% 1.81/1.01  inst_num_of_dismatching_blockings:      28
% 1.81/1.01  inst_num_of_non_proper_insts:           360
% 1.81/1.01  inst_num_of_duplicates:                 0
% 1.81/1.01  inst_inst_num_from_inst_to_res:         0
% 1.81/1.01  inst_dismatching_checking_time:         0.
% 1.81/1.01  
% 1.81/1.01  ------ Resolution
% 1.81/1.01  
% 1.81/1.01  res_num_of_clauses:                     0
% 1.81/1.01  res_num_in_passive:                     0
% 1.81/1.01  res_num_in_active:                      0
% 1.81/1.01  res_num_of_loops:                       113
% 1.81/1.01  res_forward_subset_subsumed:            37
% 1.81/1.01  res_backward_subset_subsumed:           2
% 1.81/1.01  res_forward_subsumed:                   0
% 1.81/1.01  res_backward_subsumed:                  0
% 1.81/1.01  res_forward_subsumption_resolution:     0
% 1.81/1.01  res_backward_subsumption_resolution:    0
% 1.81/1.01  res_clause_to_clause_subsumption:       157
% 1.81/1.01  res_orphan_elimination:                 0
% 1.81/1.01  res_tautology_del:                      56
% 1.81/1.01  res_num_eq_res_simplified:              4
% 1.81/1.01  res_num_sel_changes:                    0
% 1.81/1.01  res_moves_from_active_to_pass:          0
% 1.81/1.01  
% 1.81/1.01  ------ Superposition
% 1.81/1.01  
% 1.81/1.01  sup_time_total:                         0.
% 1.81/1.01  sup_time_generating:                    0.
% 1.81/1.01  sup_time_sim_full:                      0.
% 1.81/1.01  sup_time_sim_immed:                     0.
% 1.81/1.01  
% 1.81/1.01  sup_num_of_clauses:                     42
% 1.81/1.01  sup_num_in_active:                      26
% 1.81/1.01  sup_num_in_passive:                     16
% 1.81/1.01  sup_num_of_loops:                       49
% 1.81/1.01  sup_fw_superposition:                   36
% 1.81/1.01  sup_bw_superposition:                   22
% 1.81/1.01  sup_immediate_simplified:               8
% 1.81/1.01  sup_given_eliminated:                   0
% 1.81/1.01  comparisons_done:                       0
% 1.81/1.01  comparisons_avoided:                    0
% 1.81/1.01  
% 1.81/1.01  ------ Simplifications
% 1.81/1.01  
% 1.81/1.01  
% 1.81/1.01  sim_fw_subset_subsumed:                 3
% 1.81/1.01  sim_bw_subset_subsumed:                 3
% 1.81/1.01  sim_fw_subsumed:                        4
% 1.81/1.01  sim_bw_subsumed:                        0
% 1.81/1.01  sim_fw_subsumption_res:                 2
% 1.81/1.01  sim_bw_subsumption_res:                 0
% 1.81/1.01  sim_tautology_del:                      1
% 1.81/1.01  sim_eq_tautology_del:                   6
% 1.81/1.01  sim_eq_res_simp:                        0
% 1.81/1.01  sim_fw_demodulated:                     1
% 1.81/1.01  sim_bw_demodulated:                     22
% 1.81/1.01  sim_light_normalised:                   2
% 1.81/1.01  sim_joinable_taut:                      0
% 1.81/1.01  sim_joinable_simp:                      0
% 1.81/1.01  sim_ac_normalised:                      0
% 1.81/1.01  sim_smt_subsumption:                    0
% 1.81/1.01  
%------------------------------------------------------------------------------
