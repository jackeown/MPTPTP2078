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
% DateTime   : Thu Dec  3 12:12:49 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  204 (4657 expanded)
%              Number of clauses        :  130 ( 854 expanded)
%              Number of leaves         :   19 (1521 expanded)
%              Depth                    :   26
%              Number of atoms          : 1016 (44960 expanded)
%              Number of equality atoms :  210 (1038 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f46,f45,f44,f43])).

fof(f76,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
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

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f9])).

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
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_212,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_213,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_412,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_213])).

cnf(c_413,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1664,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_402,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_213])).

cnf(c_403,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_404,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_414,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2123,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2764,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_2765,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2764])).

cnf(c_23,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1668,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1669,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_587,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_588,plain,
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
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_869,plain,
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
    inference(resolution_lifted,[status(thm)],[c_588,c_25])).

cnf(c_870,plain,
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
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_874,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_29,c_28,c_27,c_26])).

cnf(c_1115,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_874])).

cnf(c_1659,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_2811,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1659])).

cnf(c_3096,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_2811])).

cnf(c_36,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_37,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2124,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_2848,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2124])).

cnf(c_2849,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2848])).

cnf(c_3199,plain,
    ( m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3096,c_36,c_37,c_414,c_2849])).

cnf(c_14,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_659,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_660,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_824,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_660,c_25])).

cnf(c_825,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_829,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_29,c_28,c_27,c_26])).

cnf(c_1123,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_829])).

cnf(c_1657,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_15,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_953,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_954,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_953])).

cnf(c_956,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_29,c_28,c_27,c_26])).

cnf(c_1662,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_1907,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1662])).

cnf(c_2052,plain,
    ( m1_orders_2(X0,sK1,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1907])).

cnf(c_3205,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_2052])).

cnf(c_4158,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_404,c_414,c_2765,c_3205])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_548,plain,
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
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_549,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_899,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_549,c_25])).

cnf(c_900,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_29,c_28,c_27,c_26])).

cnf(c_1111,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_904])).

cnf(c_1660,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_70,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_958,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_970,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_971,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_973,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_29,c_28,c_27,c_26])).

cnf(c_1661,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_1906,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1661])).

cnf(c_3478,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1660,c_70,c_958,c_1906,c_1907])).

cnf(c_3479,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3478])).

cnf(c_3486,plain,
    ( sK4 = X0
    | m1_orders_2(X0,sK1,sK4) != iProver_top
    | m1_orders_2(sK4,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_3479])).

cnf(c_4169,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_3486])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_210,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_211,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_389,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_211])).

cnf(c_390,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_391,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1820,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1821,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_1836,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_1837,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_4676,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_37,c_391,c_404,c_414,c_1821,c_1837,c_2765,c_3205])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f64])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_13])).

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

cnf(c_929,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_25])).

cnf(c_930,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_29,c_28,c_27,c_26])).

cnf(c_935,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1663,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_1905,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1663])).

cnf(c_3959,plain,
    ( sK4 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK4) != iProver_top
    | m1_orders_2(sK4,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1905])).

cnf(c_4168,plain,
    ( sK4 = k1_xboole_0
    | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_3959])).

cnf(c_4679,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4676,c_4168])).

cnf(c_4688,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4676,c_3199])).

cnf(c_4701,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4679,c_4688])).

cnf(c_17,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_626,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_627,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_845,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_627,c_25])).

cnf(c_846,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_850,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_29,c_28,c_27,c_26])).

cnf(c_1119,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_850])).

cnf(c_1658,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_2096,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1658])).

cnf(c_2607,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_2096])).

cnf(c_4866,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4701,c_2607])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1674,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1670,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1670,c_10])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_1667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_4783,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1667])).

cnf(c_4789,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_4783])).

cnf(c_5051,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4866,c_4789])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.00/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.01  
% 2.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/1.01  
% 2.00/1.01  ------  iProver source info
% 2.00/1.01  
% 2.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/1.01  git: non_committed_changes: false
% 2.00/1.01  git: last_make_outside_of_git: false
% 2.00/1.01  
% 2.00/1.01  ------ 
% 2.00/1.01  
% 2.00/1.01  ------ Input Options
% 2.00/1.01  
% 2.00/1.01  --out_options                           all
% 2.00/1.01  --tptp_safe_out                         true
% 2.00/1.01  --problem_path                          ""
% 2.00/1.01  --include_path                          ""
% 2.00/1.01  --clausifier                            res/vclausify_rel
% 2.00/1.01  --clausifier_options                    --mode clausify
% 2.00/1.01  --stdin                                 false
% 2.00/1.01  --stats_out                             all
% 2.00/1.01  
% 2.00/1.01  ------ General Options
% 2.00/1.01  
% 2.00/1.01  --fof                                   false
% 2.00/1.01  --time_out_real                         305.
% 2.00/1.01  --time_out_virtual                      -1.
% 2.00/1.01  --symbol_type_check                     false
% 2.00/1.01  --clausify_out                          false
% 2.00/1.01  --sig_cnt_out                           false
% 2.00/1.01  --trig_cnt_out                          false
% 2.00/1.01  --trig_cnt_out_tolerance                1.
% 2.00/1.01  --trig_cnt_out_sk_spl                   false
% 2.00/1.01  --abstr_cl_out                          false
% 2.00/1.01  
% 2.00/1.01  ------ Global Options
% 2.00/1.01  
% 2.00/1.01  --schedule                              default
% 2.00/1.01  --add_important_lit                     false
% 2.00/1.01  --prop_solver_per_cl                    1000
% 2.00/1.01  --min_unsat_core                        false
% 2.00/1.01  --soft_assumptions                      false
% 2.00/1.01  --soft_lemma_size                       3
% 2.00/1.01  --prop_impl_unit_size                   0
% 2.00/1.01  --prop_impl_unit                        []
% 2.00/1.01  --share_sel_clauses                     true
% 2.00/1.01  --reset_solvers                         false
% 2.00/1.01  --bc_imp_inh                            [conj_cone]
% 2.00/1.01  --conj_cone_tolerance                   3.
% 2.00/1.01  --extra_neg_conj                        none
% 2.00/1.01  --large_theory_mode                     true
% 2.00/1.01  --prolific_symb_bound                   200
% 2.00/1.01  --lt_threshold                          2000
% 2.00/1.01  --clause_weak_htbl                      true
% 2.00/1.01  --gc_record_bc_elim                     false
% 2.00/1.01  
% 2.00/1.01  ------ Preprocessing Options
% 2.00/1.01  
% 2.00/1.01  --preprocessing_flag                    true
% 2.00/1.01  --time_out_prep_mult                    0.1
% 2.00/1.01  --splitting_mode                        input
% 2.00/1.01  --splitting_grd                         true
% 2.00/1.01  --splitting_cvd                         false
% 2.00/1.01  --splitting_cvd_svl                     false
% 2.00/1.01  --splitting_nvd                         32
% 2.00/1.01  --sub_typing                            true
% 2.00/1.01  --prep_gs_sim                           true
% 2.00/1.01  --prep_unflatten                        true
% 2.00/1.01  --prep_res_sim                          true
% 2.00/1.01  --prep_upred                            true
% 2.00/1.01  --prep_sem_filter                       exhaustive
% 2.00/1.01  --prep_sem_filter_out                   false
% 2.00/1.01  --pred_elim                             true
% 2.00/1.01  --res_sim_input                         true
% 2.00/1.01  --eq_ax_congr_red                       true
% 2.00/1.01  --pure_diseq_elim                       true
% 2.00/1.01  --brand_transform                       false
% 2.00/1.01  --non_eq_to_eq                          false
% 2.00/1.01  --prep_def_merge                        true
% 2.00/1.01  --prep_def_merge_prop_impl              false
% 2.00/1.01  --prep_def_merge_mbd                    true
% 2.00/1.01  --prep_def_merge_tr_red                 false
% 2.00/1.01  --prep_def_merge_tr_cl                  false
% 2.00/1.01  --smt_preprocessing                     true
% 2.00/1.01  --smt_ac_axioms                         fast
% 2.00/1.01  --preprocessed_out                      false
% 2.00/1.01  --preprocessed_stats                    false
% 2.00/1.01  
% 2.00/1.01  ------ Abstraction refinement Options
% 2.00/1.01  
% 2.00/1.01  --abstr_ref                             []
% 2.00/1.01  --abstr_ref_prep                        false
% 2.00/1.01  --abstr_ref_until_sat                   false
% 2.00/1.01  --abstr_ref_sig_restrict                funpre
% 2.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.01  --abstr_ref_under                       []
% 2.00/1.01  
% 2.00/1.01  ------ SAT Options
% 2.00/1.01  
% 2.00/1.01  --sat_mode                              false
% 2.00/1.01  --sat_fm_restart_options                ""
% 2.00/1.01  --sat_gr_def                            false
% 2.00/1.01  --sat_epr_types                         true
% 2.00/1.01  --sat_non_cyclic_types                  false
% 2.00/1.01  --sat_finite_models                     false
% 2.00/1.01  --sat_fm_lemmas                         false
% 2.00/1.01  --sat_fm_prep                           false
% 2.00/1.02  --sat_fm_uc_incr                        true
% 2.00/1.02  --sat_out_model                         small
% 2.00/1.02  --sat_out_clauses                       false
% 2.00/1.02  
% 2.00/1.02  ------ QBF Options
% 2.00/1.02  
% 2.00/1.02  --qbf_mode                              false
% 2.00/1.02  --qbf_elim_univ                         false
% 2.00/1.02  --qbf_dom_inst                          none
% 2.00/1.02  --qbf_dom_pre_inst                      false
% 2.00/1.02  --qbf_sk_in                             false
% 2.00/1.02  --qbf_pred_elim                         true
% 2.00/1.02  --qbf_split                             512
% 2.00/1.02  
% 2.00/1.02  ------ BMC1 Options
% 2.00/1.02  
% 2.00/1.02  --bmc1_incremental                      false
% 2.00/1.02  --bmc1_axioms                           reachable_all
% 2.00/1.02  --bmc1_min_bound                        0
% 2.00/1.02  --bmc1_max_bound                        -1
% 2.00/1.02  --bmc1_max_bound_default                -1
% 2.00/1.02  --bmc1_symbol_reachability              true
% 2.00/1.02  --bmc1_property_lemmas                  false
% 2.00/1.02  --bmc1_k_induction                      false
% 2.00/1.02  --bmc1_non_equiv_states                 false
% 2.00/1.02  --bmc1_deadlock                         false
% 2.00/1.02  --bmc1_ucm                              false
% 2.00/1.02  --bmc1_add_unsat_core                   none
% 2.00/1.02  --bmc1_unsat_core_children              false
% 2.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.02  --bmc1_out_stat                         full
% 2.00/1.02  --bmc1_ground_init                      false
% 2.00/1.02  --bmc1_pre_inst_next_state              false
% 2.00/1.02  --bmc1_pre_inst_state                   false
% 2.00/1.02  --bmc1_pre_inst_reach_state             false
% 2.00/1.02  --bmc1_out_unsat_core                   false
% 2.00/1.02  --bmc1_aig_witness_out                  false
% 2.00/1.02  --bmc1_verbose                          false
% 2.00/1.02  --bmc1_dump_clauses_tptp                false
% 2.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.02  --bmc1_dump_file                        -
% 2.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.02  --bmc1_ucm_extend_mode                  1
% 2.00/1.02  --bmc1_ucm_init_mode                    2
% 2.00/1.02  --bmc1_ucm_cone_mode                    none
% 2.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.02  --bmc1_ucm_relax_model                  4
% 2.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.02  --bmc1_ucm_layered_model                none
% 2.00/1.02  --bmc1_ucm_max_lemma_size               10
% 2.00/1.02  
% 2.00/1.02  ------ AIG Options
% 2.00/1.02  
% 2.00/1.02  --aig_mode                              false
% 2.00/1.02  
% 2.00/1.02  ------ Instantiation Options
% 2.00/1.02  
% 2.00/1.02  --instantiation_flag                    true
% 2.00/1.02  --inst_sos_flag                         false
% 2.00/1.02  --inst_sos_phase                        true
% 2.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.02  --inst_lit_sel_side                     num_symb
% 2.00/1.02  --inst_solver_per_active                1400
% 2.00/1.02  --inst_solver_calls_frac                1.
% 2.00/1.02  --inst_passive_queue_type               priority_queues
% 2.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.02  --inst_passive_queues_freq              [25;2]
% 2.00/1.02  --inst_dismatching                      true
% 2.00/1.02  --inst_eager_unprocessed_to_passive     true
% 2.00/1.02  --inst_prop_sim_given                   true
% 2.00/1.02  --inst_prop_sim_new                     false
% 2.00/1.02  --inst_subs_new                         false
% 2.00/1.02  --inst_eq_res_simp                      false
% 2.00/1.02  --inst_subs_given                       false
% 2.00/1.02  --inst_orphan_elimination               true
% 2.00/1.02  --inst_learning_loop_flag               true
% 2.00/1.02  --inst_learning_start                   3000
% 2.00/1.02  --inst_learning_factor                  2
% 2.00/1.02  --inst_start_prop_sim_after_learn       3
% 2.00/1.02  --inst_sel_renew                        solver
% 2.00/1.02  --inst_lit_activity_flag                true
% 2.00/1.02  --inst_restr_to_given                   false
% 2.00/1.02  --inst_activity_threshold               500
% 2.00/1.02  --inst_out_proof                        true
% 2.00/1.02  
% 2.00/1.02  ------ Resolution Options
% 2.00/1.02  
% 2.00/1.02  --resolution_flag                       true
% 2.00/1.02  --res_lit_sel                           adaptive
% 2.00/1.02  --res_lit_sel_side                      none
% 2.00/1.02  --res_ordering                          kbo
% 2.00/1.02  --res_to_prop_solver                    active
% 2.00/1.02  --res_prop_simpl_new                    false
% 2.00/1.02  --res_prop_simpl_given                  true
% 2.00/1.02  --res_passive_queue_type                priority_queues
% 2.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.02  --res_passive_queues_freq               [15;5]
% 2.00/1.02  --res_forward_subs                      full
% 2.00/1.02  --res_backward_subs                     full
% 2.00/1.02  --res_forward_subs_resolution           true
% 2.00/1.02  --res_backward_subs_resolution          true
% 2.00/1.02  --res_orphan_elimination                true
% 2.00/1.02  --res_time_limit                        2.
% 2.00/1.02  --res_out_proof                         true
% 2.00/1.02  
% 2.00/1.02  ------ Superposition Options
% 2.00/1.02  
% 2.00/1.02  --superposition_flag                    true
% 2.00/1.02  --sup_passive_queue_type                priority_queues
% 2.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.02  --demod_completeness_check              fast
% 2.00/1.02  --demod_use_ground                      true
% 2.00/1.02  --sup_to_prop_solver                    passive
% 2.00/1.02  --sup_prop_simpl_new                    true
% 2.00/1.02  --sup_prop_simpl_given                  true
% 2.00/1.02  --sup_fun_splitting                     false
% 2.00/1.02  --sup_smt_interval                      50000
% 2.00/1.02  
% 2.00/1.02  ------ Superposition Simplification Setup
% 2.00/1.02  
% 2.00/1.02  --sup_indices_passive                   []
% 2.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_full_bw                           [BwDemod]
% 2.00/1.02  --sup_immed_triv                        [TrivRules]
% 2.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_immed_bw_main                     []
% 2.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.02  
% 2.00/1.02  ------ Combination Options
% 2.00/1.02  
% 2.00/1.02  --comb_res_mult                         3
% 2.00/1.02  --comb_sup_mult                         2
% 2.00/1.02  --comb_inst_mult                        10
% 2.00/1.02  
% 2.00/1.02  ------ Debug Options
% 2.00/1.02  
% 2.00/1.02  --dbg_backtrace                         false
% 2.00/1.02  --dbg_dump_prop_clauses                 false
% 2.00/1.02  --dbg_dump_prop_clauses_file            -
% 2.00/1.02  --dbg_out_stat                          false
% 2.00/1.02  ------ Parsing...
% 2.00/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/1.02  
% 2.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.00/1.02  
% 2.00/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/1.02  
% 2.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.00/1.02  ------ Proving...
% 2.00/1.02  ------ Problem Properties 
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  clauses                                 20
% 2.00/1.02  conjectures                             2
% 2.00/1.02  EPR                                     11
% 2.00/1.02  Horn                                    16
% 2.00/1.02  unary                                   5
% 2.00/1.02  binary                                  6
% 2.00/1.02  lits                                    49
% 2.00/1.02  lits eq                                 7
% 2.00/1.02  fd_pure                                 0
% 2.00/1.02  fd_pseudo                               0
% 2.00/1.02  fd_cond                                 1
% 2.00/1.02  fd_pseudo_cond                          3
% 2.00/1.02  AC symbols                              0
% 2.00/1.02  
% 2.00/1.02  ------ Schedule dynamic 5 is on 
% 2.00/1.02  
% 2.00/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  ------ 
% 2.00/1.02  Current options:
% 2.00/1.02  ------ 
% 2.00/1.02  
% 2.00/1.02  ------ Input Options
% 2.00/1.02  
% 2.00/1.02  --out_options                           all
% 2.00/1.02  --tptp_safe_out                         true
% 2.00/1.02  --problem_path                          ""
% 2.00/1.02  --include_path                          ""
% 2.00/1.02  --clausifier                            res/vclausify_rel
% 2.00/1.02  --clausifier_options                    --mode clausify
% 2.00/1.02  --stdin                                 false
% 2.00/1.02  --stats_out                             all
% 2.00/1.02  
% 2.00/1.02  ------ General Options
% 2.00/1.02  
% 2.00/1.02  --fof                                   false
% 2.00/1.02  --time_out_real                         305.
% 2.00/1.02  --time_out_virtual                      -1.
% 2.00/1.02  --symbol_type_check                     false
% 2.00/1.02  --clausify_out                          false
% 2.00/1.02  --sig_cnt_out                           false
% 2.00/1.02  --trig_cnt_out                          false
% 2.00/1.02  --trig_cnt_out_tolerance                1.
% 2.00/1.02  --trig_cnt_out_sk_spl                   false
% 2.00/1.02  --abstr_cl_out                          false
% 2.00/1.02  
% 2.00/1.02  ------ Global Options
% 2.00/1.02  
% 2.00/1.02  --schedule                              default
% 2.00/1.02  --add_important_lit                     false
% 2.00/1.02  --prop_solver_per_cl                    1000
% 2.00/1.02  --min_unsat_core                        false
% 2.00/1.02  --soft_assumptions                      false
% 2.00/1.02  --soft_lemma_size                       3
% 2.00/1.02  --prop_impl_unit_size                   0
% 2.00/1.02  --prop_impl_unit                        []
% 2.00/1.02  --share_sel_clauses                     true
% 2.00/1.02  --reset_solvers                         false
% 2.00/1.02  --bc_imp_inh                            [conj_cone]
% 2.00/1.02  --conj_cone_tolerance                   3.
% 2.00/1.02  --extra_neg_conj                        none
% 2.00/1.02  --large_theory_mode                     true
% 2.00/1.02  --prolific_symb_bound                   200
% 2.00/1.02  --lt_threshold                          2000
% 2.00/1.02  --clause_weak_htbl                      true
% 2.00/1.02  --gc_record_bc_elim                     false
% 2.00/1.02  
% 2.00/1.02  ------ Preprocessing Options
% 2.00/1.02  
% 2.00/1.02  --preprocessing_flag                    true
% 2.00/1.02  --time_out_prep_mult                    0.1
% 2.00/1.02  --splitting_mode                        input
% 2.00/1.02  --splitting_grd                         true
% 2.00/1.02  --splitting_cvd                         false
% 2.00/1.02  --splitting_cvd_svl                     false
% 2.00/1.02  --splitting_nvd                         32
% 2.00/1.02  --sub_typing                            true
% 2.00/1.02  --prep_gs_sim                           true
% 2.00/1.02  --prep_unflatten                        true
% 2.00/1.02  --prep_res_sim                          true
% 2.00/1.02  --prep_upred                            true
% 2.00/1.02  --prep_sem_filter                       exhaustive
% 2.00/1.02  --prep_sem_filter_out                   false
% 2.00/1.02  --pred_elim                             true
% 2.00/1.02  --res_sim_input                         true
% 2.00/1.02  --eq_ax_congr_red                       true
% 2.00/1.02  --pure_diseq_elim                       true
% 2.00/1.02  --brand_transform                       false
% 2.00/1.02  --non_eq_to_eq                          false
% 2.00/1.02  --prep_def_merge                        true
% 2.00/1.02  --prep_def_merge_prop_impl              false
% 2.00/1.02  --prep_def_merge_mbd                    true
% 2.00/1.02  --prep_def_merge_tr_red                 false
% 2.00/1.02  --prep_def_merge_tr_cl                  false
% 2.00/1.02  --smt_preprocessing                     true
% 2.00/1.02  --smt_ac_axioms                         fast
% 2.00/1.02  --preprocessed_out                      false
% 2.00/1.02  --preprocessed_stats                    false
% 2.00/1.02  
% 2.00/1.02  ------ Abstraction refinement Options
% 2.00/1.02  
% 2.00/1.02  --abstr_ref                             []
% 2.00/1.02  --abstr_ref_prep                        false
% 2.00/1.02  --abstr_ref_until_sat                   false
% 2.00/1.02  --abstr_ref_sig_restrict                funpre
% 2.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.02  --abstr_ref_under                       []
% 2.00/1.02  
% 2.00/1.02  ------ SAT Options
% 2.00/1.02  
% 2.00/1.02  --sat_mode                              false
% 2.00/1.02  --sat_fm_restart_options                ""
% 2.00/1.02  --sat_gr_def                            false
% 2.00/1.02  --sat_epr_types                         true
% 2.00/1.02  --sat_non_cyclic_types                  false
% 2.00/1.02  --sat_finite_models                     false
% 2.00/1.02  --sat_fm_lemmas                         false
% 2.00/1.02  --sat_fm_prep                           false
% 2.00/1.02  --sat_fm_uc_incr                        true
% 2.00/1.02  --sat_out_model                         small
% 2.00/1.02  --sat_out_clauses                       false
% 2.00/1.02  
% 2.00/1.02  ------ QBF Options
% 2.00/1.02  
% 2.00/1.02  --qbf_mode                              false
% 2.00/1.02  --qbf_elim_univ                         false
% 2.00/1.02  --qbf_dom_inst                          none
% 2.00/1.02  --qbf_dom_pre_inst                      false
% 2.00/1.02  --qbf_sk_in                             false
% 2.00/1.02  --qbf_pred_elim                         true
% 2.00/1.02  --qbf_split                             512
% 2.00/1.02  
% 2.00/1.02  ------ BMC1 Options
% 2.00/1.02  
% 2.00/1.02  --bmc1_incremental                      false
% 2.00/1.02  --bmc1_axioms                           reachable_all
% 2.00/1.02  --bmc1_min_bound                        0
% 2.00/1.02  --bmc1_max_bound                        -1
% 2.00/1.02  --bmc1_max_bound_default                -1
% 2.00/1.02  --bmc1_symbol_reachability              true
% 2.00/1.02  --bmc1_property_lemmas                  false
% 2.00/1.02  --bmc1_k_induction                      false
% 2.00/1.02  --bmc1_non_equiv_states                 false
% 2.00/1.02  --bmc1_deadlock                         false
% 2.00/1.02  --bmc1_ucm                              false
% 2.00/1.02  --bmc1_add_unsat_core                   none
% 2.00/1.02  --bmc1_unsat_core_children              false
% 2.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.02  --bmc1_out_stat                         full
% 2.00/1.02  --bmc1_ground_init                      false
% 2.00/1.02  --bmc1_pre_inst_next_state              false
% 2.00/1.02  --bmc1_pre_inst_state                   false
% 2.00/1.02  --bmc1_pre_inst_reach_state             false
% 2.00/1.02  --bmc1_out_unsat_core                   false
% 2.00/1.02  --bmc1_aig_witness_out                  false
% 2.00/1.02  --bmc1_verbose                          false
% 2.00/1.02  --bmc1_dump_clauses_tptp                false
% 2.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.02  --bmc1_dump_file                        -
% 2.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.02  --bmc1_ucm_extend_mode                  1
% 2.00/1.02  --bmc1_ucm_init_mode                    2
% 2.00/1.02  --bmc1_ucm_cone_mode                    none
% 2.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.02  --bmc1_ucm_relax_model                  4
% 2.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.02  --bmc1_ucm_layered_model                none
% 2.00/1.02  --bmc1_ucm_max_lemma_size               10
% 2.00/1.02  
% 2.00/1.02  ------ AIG Options
% 2.00/1.02  
% 2.00/1.02  --aig_mode                              false
% 2.00/1.02  
% 2.00/1.02  ------ Instantiation Options
% 2.00/1.02  
% 2.00/1.02  --instantiation_flag                    true
% 2.00/1.02  --inst_sos_flag                         false
% 2.00/1.02  --inst_sos_phase                        true
% 2.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.02  --inst_lit_sel_side                     none
% 2.00/1.02  --inst_solver_per_active                1400
% 2.00/1.02  --inst_solver_calls_frac                1.
% 2.00/1.02  --inst_passive_queue_type               priority_queues
% 2.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.02  --inst_passive_queues_freq              [25;2]
% 2.00/1.02  --inst_dismatching                      true
% 2.00/1.02  --inst_eager_unprocessed_to_passive     true
% 2.00/1.02  --inst_prop_sim_given                   true
% 2.00/1.02  --inst_prop_sim_new                     false
% 2.00/1.02  --inst_subs_new                         false
% 2.00/1.02  --inst_eq_res_simp                      false
% 2.00/1.02  --inst_subs_given                       false
% 2.00/1.02  --inst_orphan_elimination               true
% 2.00/1.02  --inst_learning_loop_flag               true
% 2.00/1.02  --inst_learning_start                   3000
% 2.00/1.02  --inst_learning_factor                  2
% 2.00/1.02  --inst_start_prop_sim_after_learn       3
% 2.00/1.02  --inst_sel_renew                        solver
% 2.00/1.02  --inst_lit_activity_flag                true
% 2.00/1.02  --inst_restr_to_given                   false
% 2.00/1.02  --inst_activity_threshold               500
% 2.00/1.02  --inst_out_proof                        true
% 2.00/1.02  
% 2.00/1.02  ------ Resolution Options
% 2.00/1.02  
% 2.00/1.02  --resolution_flag                       false
% 2.00/1.02  --res_lit_sel                           adaptive
% 2.00/1.02  --res_lit_sel_side                      none
% 2.00/1.02  --res_ordering                          kbo
% 2.00/1.02  --res_to_prop_solver                    active
% 2.00/1.02  --res_prop_simpl_new                    false
% 2.00/1.02  --res_prop_simpl_given                  true
% 2.00/1.02  --res_passive_queue_type                priority_queues
% 2.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.02  --res_passive_queues_freq               [15;5]
% 2.00/1.02  --res_forward_subs                      full
% 2.00/1.02  --res_backward_subs                     full
% 2.00/1.02  --res_forward_subs_resolution           true
% 2.00/1.02  --res_backward_subs_resolution          true
% 2.00/1.02  --res_orphan_elimination                true
% 2.00/1.02  --res_time_limit                        2.
% 2.00/1.02  --res_out_proof                         true
% 2.00/1.02  
% 2.00/1.02  ------ Superposition Options
% 2.00/1.02  
% 2.00/1.02  --superposition_flag                    true
% 2.00/1.02  --sup_passive_queue_type                priority_queues
% 2.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.02  --demod_completeness_check              fast
% 2.00/1.02  --demod_use_ground                      true
% 2.00/1.02  --sup_to_prop_solver                    passive
% 2.00/1.02  --sup_prop_simpl_new                    true
% 2.00/1.02  --sup_prop_simpl_given                  true
% 2.00/1.02  --sup_fun_splitting                     false
% 2.00/1.02  --sup_smt_interval                      50000
% 2.00/1.02  
% 2.00/1.02  ------ Superposition Simplification Setup
% 2.00/1.02  
% 2.00/1.02  --sup_indices_passive                   []
% 2.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_full_bw                           [BwDemod]
% 2.00/1.02  --sup_immed_triv                        [TrivRules]
% 2.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_immed_bw_main                     []
% 2.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.02  
% 2.00/1.02  ------ Combination Options
% 2.00/1.02  
% 2.00/1.02  --comb_res_mult                         3
% 2.00/1.02  --comb_sup_mult                         2
% 2.00/1.02  --comb_inst_mult                        10
% 2.00/1.02  
% 2.00/1.02  ------ Debug Options
% 2.00/1.02  
% 2.00/1.02  --dbg_backtrace                         false
% 2.00/1.02  --dbg_dump_prop_clauses                 false
% 2.00/1.02  --dbg_dump_prop_clauses_file            -
% 2.00/1.02  --dbg_out_stat                          false
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  ------ Proving...
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  % SZS status Theorem for theBenchmark.p
% 2.00/1.02  
% 2.00/1.02   Resolution empty clause
% 2.00/1.02  
% 2.00/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.00/1.02  
% 2.00/1.02  fof(f1,axiom,(
% 2.00/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f34,plain,(
% 2.00/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.00/1.02    inference(nnf_transformation,[],[f1])).
% 2.00/1.02  
% 2.00/1.02  fof(f35,plain,(
% 2.00/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.00/1.02    inference(flattening,[],[f34])).
% 2.00/1.02  
% 2.00/1.02  fof(f49,plain,(
% 2.00/1.02    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f35])).
% 2.00/1.02  
% 2.00/1.02  fof(f78,plain,(
% 2.00/1.02    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.00/1.02    inference(equality_resolution,[],[f49])).
% 2.00/1.02  
% 2.00/1.02  fof(f14,conjecture,(
% 2.00/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f15,negated_conjecture,(
% 2.00/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.00/1.02    inference(negated_conjecture,[],[f14])).
% 2.00/1.02  
% 2.00/1.02  fof(f32,plain,(
% 2.00/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f15])).
% 2.00/1.02  
% 2.00/1.02  fof(f33,plain,(
% 2.00/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f32])).
% 2.00/1.02  
% 2.00/1.02  fof(f41,plain,(
% 2.00/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.00/1.02    inference(nnf_transformation,[],[f33])).
% 2.00/1.02  
% 2.00/1.02  fof(f42,plain,(
% 2.00/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f41])).
% 2.00/1.02  
% 2.00/1.02  fof(f46,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 2.00/1.02    introduced(choice_axiom,[])).
% 2.00/1.02  
% 2.00/1.02  fof(f45,plain,(
% 2.00/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 2.00/1.02    introduced(choice_axiom,[])).
% 2.00/1.02  
% 2.00/1.02  fof(f44,plain,(
% 2.00/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 2.00/1.02    introduced(choice_axiom,[])).
% 2.00/1.02  
% 2.00/1.02  fof(f43,plain,(
% 2.00/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.00/1.02    introduced(choice_axiom,[])).
% 2.00/1.02  
% 2.00/1.02  fof(f47,plain,(
% 2.00/1.02    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f46,f45,f44,f43])).
% 2.00/1.02  
% 2.00/1.02  fof(f76,plain,(
% 2.00/1.02    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f48,plain,(
% 2.00/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f35])).
% 2.00/1.02  
% 2.00/1.02  fof(f4,axiom,(
% 2.00/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f38,plain,(
% 2.00/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/1.02    inference(nnf_transformation,[],[f4])).
% 2.00/1.02  
% 2.00/1.02  fof(f39,plain,(
% 2.00/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/1.02    inference(flattening,[],[f38])).
% 2.00/1.02  
% 2.00/1.02  fof(f57,plain,(
% 2.00/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f39])).
% 2.00/1.02  
% 2.00/1.02  fof(f74,plain,(
% 2.00/1.02    m2_orders_2(sK3,sK1,sK2)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f75,plain,(
% 2.00/1.02    m2_orders_2(sK4,sK1,sK2)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f13,axiom,(
% 2.00/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f30,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f13])).
% 2.00/1.02  
% 2.00/1.02  fof(f31,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f30])).
% 2.00/1.02  
% 2.00/1.02  fof(f40,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(nnf_transformation,[],[f31])).
% 2.00/1.02  
% 2.00/1.02  fof(f67,plain,(
% 2.00/1.02    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f40])).
% 2.00/1.02  
% 2.00/1.02  fof(f73,plain,(
% 2.00/1.02    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f72,plain,(
% 2.00/1.02    l1_orders_2(sK1)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f68,plain,(
% 2.00/1.02    ~v2_struct_0(sK1)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f69,plain,(
% 2.00/1.02    v3_orders_2(sK1)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f70,plain,(
% 2.00/1.02    v4_orders_2(sK1)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f71,plain,(
% 2.00/1.02    v5_orders_2(sK1)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f9,axiom,(
% 2.00/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f17,plain,(
% 2.00/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.00/1.02  
% 2.00/1.02  fof(f22,plain,(
% 2.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f17])).
% 2.00/1.02  
% 2.00/1.02  fof(f23,plain,(
% 2.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f22])).
% 2.00/1.02  
% 2.00/1.02  fof(f62,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f23])).
% 2.00/1.02  
% 2.00/1.02  fof(f10,axiom,(
% 2.00/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f24,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f10])).
% 2.00/1.02  
% 2.00/1.02  fof(f25,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f24])).
% 2.00/1.02  
% 2.00/1.02  fof(f63,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f25])).
% 2.00/1.02  
% 2.00/1.02  fof(f66,plain,(
% 2.00/1.02    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f40])).
% 2.00/1.02  
% 2.00/1.02  fof(f8,axiom,(
% 2.00/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f20,plain,(
% 2.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f8])).
% 2.00/1.02  
% 2.00/1.02  fof(f21,plain,(
% 2.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f20])).
% 2.00/1.02  
% 2.00/1.02  fof(f61,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f21])).
% 2.00/1.02  
% 2.00/1.02  fof(f50,plain,(
% 2.00/1.02    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f35])).
% 2.00/1.02  
% 2.00/1.02  fof(f77,plain,(
% 2.00/1.02    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 2.00/1.02    inference(cnf_transformation,[],[f47])).
% 2.00/1.02  
% 2.00/1.02  fof(f11,axiom,(
% 2.00/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f26,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f11])).
% 2.00/1.02  
% 2.00/1.02  fof(f27,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f26])).
% 2.00/1.02  
% 2.00/1.02  fof(f64,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f27])).
% 2.00/1.02  
% 2.00/1.02  fof(f12,axiom,(
% 2.00/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f28,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.00/1.02    inference(ennf_transformation,[],[f12])).
% 2.00/1.02  
% 2.00/1.02  fof(f29,plain,(
% 2.00/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.00/1.02    inference(flattening,[],[f28])).
% 2.00/1.02  
% 2.00/1.02  fof(f65,plain,(
% 2.00/1.02    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f29])).
% 2.00/1.02  
% 2.00/1.02  fof(f3,axiom,(
% 2.00/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f16,plain,(
% 2.00/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.00/1.02    inference(rectify,[],[f3])).
% 2.00/1.02  
% 2.00/1.02  fof(f18,plain,(
% 2.00/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.00/1.02    inference(ennf_transformation,[],[f16])).
% 2.00/1.02  
% 2.00/1.02  fof(f36,plain,(
% 2.00/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.00/1.02    introduced(choice_axiom,[])).
% 2.00/1.02  
% 2.00/1.02  fof(f37,plain,(
% 2.00/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f36])).
% 2.00/1.02  
% 2.00/1.02  fof(f53,plain,(
% 2.00/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f37])).
% 2.00/1.02  
% 2.00/1.02  fof(f6,axiom,(
% 2.00/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f59,plain,(
% 2.00/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.00/1.02    inference(cnf_transformation,[],[f6])).
% 2.00/1.02  
% 2.00/1.02  fof(f5,axiom,(
% 2.00/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f58,plain,(
% 2.00/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.00/1.02    inference(cnf_transformation,[],[f5])).
% 2.00/1.02  
% 2.00/1.02  fof(f2,axiom,(
% 2.00/1.02    v1_xboole_0(k1_xboole_0)),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f51,plain,(
% 2.00/1.02    v1_xboole_0(k1_xboole_0)),
% 2.00/1.02    inference(cnf_transformation,[],[f2])).
% 2.00/1.02  
% 2.00/1.02  fof(f7,axiom,(
% 2.00/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.00/1.02  
% 2.00/1.02  fof(f19,plain,(
% 2.00/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.00/1.02    inference(ennf_transformation,[],[f7])).
% 2.00/1.02  
% 2.00/1.02  fof(f60,plain,(
% 2.00/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.00/1.02    inference(cnf_transformation,[],[f19])).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1,plain,
% 2.00/1.02      ( ~ r2_xboole_0(X0,X0) ),
% 2.00/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_21,negated_conjecture,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.00/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_212,plain,
% 2.00/1.02      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 2.00/1.02      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_213,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 2.00/1.02      inference(renaming,[status(thm)],[c_212]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_412,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_213]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_413,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_412]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1664,plain,
% 2.00/1.02      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2,plain,
% 2.00/1.02      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_402,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(X0,X1) | sK4 != X1 | sK3 != X0 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_213]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_403,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_402]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_404,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 2.00/1.02      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_414,plain,
% 2.00/1.02      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_7,plain,
% 2.00/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.00/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2123,plain,
% 2.00/1.02      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2764,plain,
% 2.00/1.02      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_2123]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2765,plain,
% 2.00/1.02      ( sK3 = sK4
% 2.00/1.02      | r1_tarski(sK4,sK3) != iProver_top
% 2.00/1.02      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2764]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_23,negated_conjecture,
% 2.00/1.02      ( m2_orders_2(sK3,sK1,sK2) ),
% 2.00/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1668,plain,
% 2.00/1.02      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_22,negated_conjecture,
% 2.00/1.02      ( m2_orders_2(sK4,sK1,sK2) ),
% 2.00/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1669,plain,
% 2.00/1.02      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_18,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | m1_orders_2(X3,X1,X0)
% 2.00/1.02      | m1_orders_2(X0,X1,X3)
% 2.00/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X3 = X0 ),
% 2.00/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_24,negated_conjecture,
% 2.00/1.02      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 2.00/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_587,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | m1_orders_2(X3,X1,X0)
% 2.00/1.02      | m1_orders_2(X0,X1,X3)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X3 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK2 != X2 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_588,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | m1_orders_2(X0,X1,X2)
% 2.00/1.02      | m1_orders_2(X2,X1,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X0 = X2
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_587]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_25,negated_conjecture,
% 2.00/1.02      ( l1_orders_2(sK1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_869,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | m1_orders_2(X0,X1,X2)
% 2.00/1.02      | m1_orders_2(X2,X1,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | X2 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_588,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_870,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1)
% 2.00/1.02      | X1 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_869]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_29,negated_conjecture,
% 2.00/1.02      ( ~ v2_struct_0(sK1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_28,negated_conjecture,
% 2.00/1.02      ( v3_orders_2(sK1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_27,negated_conjecture,
% 2.00/1.02      ( v4_orders_2(sK1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_26,negated_conjecture,
% 2.00/1.02      ( v5_orders_2(sK1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_874,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | X1 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_870,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1115,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | X1 = X0 ),
% 2.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_874]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1659,plain,
% 2.00/1.02      ( X0 = X1
% 2.00/1.02      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) = iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2811,plain,
% 2.00/1.02      ( sK4 = X0
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 2.00/1.02      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1669,c_1659]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3096,plain,
% 2.00/1.02      ( sK4 = sK3
% 2.00/1.02      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.00/1.02      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1668,c_2811]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_36,plain,
% 2.00/1.02      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_37,plain,
% 2.00/1.02      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2124,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(sK4,sK1,sK2)
% 2.00/1.02      | m1_orders_2(X0,sK1,sK4)
% 2.00/1.02      | m1_orders_2(sK4,sK1,X0)
% 2.00/1.02      | X0 = sK4 ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2848,plain,
% 2.00/1.02      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(sK3,sK1,sK2)
% 2.00/1.02      | m1_orders_2(sK4,sK1,sK3)
% 2.00/1.02      | m1_orders_2(sK3,sK1,sK4)
% 2.00/1.02      | sK3 = sK4 ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_2124]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2849,plain,
% 2.00/1.02      ( sK3 = sK4
% 2.00/1.02      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.00/1.02      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.00/1.02      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2848]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3199,plain,
% 2.00/1.02      ( m1_orders_2(sK4,sK1,sK3) = iProver_top
% 2.00/1.02      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_3096,c_36,c_37,c_414,c_2849]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_14,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_659,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK2 != X2 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_660,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_659]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_824,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_660,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_825,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_824]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_829,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_825,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1123,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_829]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1657,plain,
% 2.00/1.02      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_15,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | r1_tarski(X0,X2)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_953,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | r1_tarski(X0,X2)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_954,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | r1_tarski(X0,X1)
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_953]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_956,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | r1_tarski(X0,X1) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_954,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1662,plain,
% 2.00/1.02      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.00/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1907,plain,
% 2.00/1.02      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.00/1.02      | r1_tarski(X1,X0) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1657,c_1662]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2052,plain,
% 2.00/1.02      ( m1_orders_2(X0,sK1,sK3) != iProver_top
% 2.00/1.02      | r1_tarski(X0,sK3) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1668,c_1907]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3205,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 2.00/1.02      | r1_tarski(sK4,sK3) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_3199,c_2052]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4158,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_1664,c_404,c_414,c_2765,c_3205]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_19,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X3,X1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,X1,X3)
% 2.00/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X3 = X0 ),
% 2.00/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_548,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X3,X1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,X1,X3)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X3 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK2 != X2 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_549,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | X0 = X2
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_548]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_899,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | X2 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_549,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_900,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1)
% 2.00/1.02      | X1 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_899]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_904,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | X1 = X0
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_900,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1111,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | X1 = X0 ),
% 2.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_904]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1660,plain,
% 2.00/1.02      ( X0 = X1
% 2.00/1.02      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_70,plain,
% 2.00/1.02      ( X0 = X1
% 2.00/1.02      | r1_tarski(X1,X0) != iProver_top
% 2.00/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_958,plain,
% 2.00/1.02      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.00/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_13,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_970,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_971,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_970]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_973,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_971,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1661,plain,
% 2.00/1.02      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1906,plain,
% 2.00/1.02      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.00/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1657,c_1661]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3478,plain,
% 2.00/1.02      ( X0 = X1
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) != iProver_top ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_1660,c_70,c_958,c_1906,c_1907]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3479,plain,
% 2.00/1.02      ( X0 = X1
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.00/1.02      inference(renaming,[status(thm)],[c_3478]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3486,plain,
% 2.00/1.02      ( sK4 = X0
% 2.00/1.02      | m1_orders_2(X0,sK1,sK4) != iProver_top
% 2.00/1.02      | m1_orders_2(sK4,sK1,X0) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1669,c_3479]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4169,plain,
% 2.00/1.02      ( sK4 = sK3 | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_4158,c_3486]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_0,plain,
% 2.00/1.02      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.00/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_20,negated_conjecture,
% 2.00/1.02      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.00/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_210,plain,
% 2.00/1.02      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 2.00/1.02      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_211,plain,
% 2.00/1.02      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 2.00/1.02      inference(renaming,[status(thm)],[c_210]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_389,plain,
% 2.00/1.02      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.00/1.02      | ~ r1_tarski(X0,X1)
% 2.00/1.02      | X1 = X0
% 2.00/1.02      | sK4 != X1
% 2.00/1.02      | sK3 != X0 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_211]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_390,plain,
% 2.00/1.02      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_389]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_391,plain,
% 2.00/1.02      ( sK4 = sK3
% 2.00/1.02      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.00/1.02      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1820,plain,
% 2.00/1.02      ( ~ m2_orders_2(sK4,sK1,sK2)
% 2.00/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_1123]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1821,plain,
% 2.00/1.02      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1836,plain,
% 2.00/1.02      ( ~ m1_orders_2(sK3,sK1,sK4)
% 2.00/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | r1_tarski(sK3,sK4) ),
% 2.00/1.02      inference(instantiation,[status(thm)],[c_956]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1837,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 2.00/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.00/1.02      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1836]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4676,plain,
% 2.00/1.02      ( sK4 = sK3 ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_4169,c_37,c_391,c_404,c_414,c_1821,c_1837,c_2765,c_3205]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_16,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_xboole_0 = X2 ),
% 2.00/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_158,plain,
% 2.00/1.02      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_xboole_0 = X2 ),
% 2.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_16,c_13]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_159,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_xboole_0 = X2 ),
% 2.00/1.02      inference(renaming,[status(thm)],[c_158]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_929,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m1_orders_2(X2,X1,X0)
% 2.00/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | sK1 != X1
% 2.00/1.02      | k1_xboole_0 = X2 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_159,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_930,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1)
% 2.00/1.02      | k1_xboole_0 = X0 ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_929]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_934,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | k1_xboole_0 = X0 ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_930,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_935,plain,
% 2.00/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.00/1.02      | ~ m1_orders_2(X1,sK1,X0)
% 2.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.02      | k1_xboole_0 = X1 ),
% 2.00/1.02      inference(renaming,[status(thm)],[c_934]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1663,plain,
% 2.00/1.02      ( k1_xboole_0 = X0
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1905,plain,
% 2.00/1.02      ( k1_xboole_0 = X0
% 2.00/1.02      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m1_orders_2(X0,sK1,X1) != iProver_top
% 2.00/1.02      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1657,c_1663]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3959,plain,
% 2.00/1.02      ( sK4 = k1_xboole_0
% 2.00/1.02      | m1_orders_2(X0,sK1,sK4) != iProver_top
% 2.00/1.02      | m1_orders_2(sK4,sK1,X0) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1669,c_1905]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4168,plain,
% 2.00/1.02      ( sK4 = k1_xboole_0 | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_4158,c_3959]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4679,plain,
% 2.00/1.02      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 2.00/1.02      inference(demodulation,[status(thm)],[c_4676,c_4168]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4688,plain,
% 2.00/1.02      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 2.00/1.02      inference(demodulation,[status(thm)],[c_4676,c_3199]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4701,plain,
% 2.00/1.02      ( sK3 = k1_xboole_0 ),
% 2.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4679,c_4688]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_17,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.00/1.02      | ~ r1_xboole_0(X0,X3)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_626,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,X2)
% 2.00/1.02      | ~ m2_orders_2(X3,X1,X2)
% 2.00/1.02      | ~ r1_xboole_0(X0,X3)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK2 != X2 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_627,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | ~ r1_xboole_0(X2,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | ~ l1_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_626]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_845,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,X1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X2,X1,sK2)
% 2.00/1.02      | ~ r1_xboole_0(X2,X0)
% 2.00/1.02      | v2_struct_0(X1)
% 2.00/1.02      | ~ v3_orders_2(X1)
% 2.00/1.02      | ~ v4_orders_2(X1)
% 2.00/1.02      | ~ v5_orders_2(X1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 2.00/1.02      | sK1 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_627,c_25]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_846,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ r1_xboole_0(X1,X0)
% 2.00/1.02      | v2_struct_0(sK1)
% 2.00/1.02      | ~ v3_orders_2(sK1)
% 2.00/1.02      | ~ v4_orders_2(sK1)
% 2.00/1.02      | ~ v5_orders_2(sK1)
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_845]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_850,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ r1_xboole_0(X1,X0)
% 2.00/1.02      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 2.00/1.02      inference(global_propositional_subsumption,
% 2.00/1.02                [status(thm)],
% 2.00/1.02                [c_846,c_29,c_28,c_27,c_26]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1119,plain,
% 2.00/1.02      ( ~ m2_orders_2(X0,sK1,sK2)
% 2.00/1.02      | ~ m2_orders_2(X1,sK1,sK2)
% 2.00/1.02      | ~ r1_xboole_0(X1,X0) ),
% 2.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_850]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1658,plain,
% 2.00/1.02      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 2.00/1.02      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2096,plain,
% 2.00/1.02      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 2.00/1.02      | r1_xboole_0(X0,sK3) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1668,c_1658]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_2607,plain,
% 2.00/1.02      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1668,c_2096]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4866,plain,
% 2.00/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.00/1.02      inference(demodulation,[status(thm)],[c_4701,c_2607]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_5,plain,
% 2.00/1.02      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1674,plain,
% 2.00/1.02      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.00/1.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_11,plain,
% 2.00/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.00/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1670,plain,
% 2.00/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_10,plain,
% 2.00/1.02      ( k2_subset_1(X0) = X0 ),
% 2.00/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1684,plain,
% 2.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.00/1.02      inference(light_normalisation,[status(thm)],[c_1670,c_10]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_3,plain,
% 2.00/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.00/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_12,plain,
% 2.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.00/1.02      | ~ r2_hidden(X2,X0)
% 2.00/1.02      | ~ v1_xboole_0(X1) ),
% 2.00/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_370,plain,
% 2.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.00/1.02      | ~ r2_hidden(X2,X0)
% 2.00/1.02      | k1_xboole_0 != X1 ),
% 2.00/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_371,plain,
% 2.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 2.00/1.02      inference(unflattening,[status(thm)],[c_370]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_1667,plain,
% 2.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.00/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 2.00/1.02      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4783,plain,
% 2.00/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1684,c_1667]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_4789,plain,
% 2.00/1.02      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.00/1.02      inference(superposition,[status(thm)],[c_1674,c_4783]) ).
% 2.00/1.02  
% 2.00/1.02  cnf(c_5051,plain,
% 2.00/1.02      ( $false ),
% 2.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4866,c_4789]) ).
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.00/1.02  
% 2.00/1.02  ------                               Statistics
% 2.00/1.02  
% 2.00/1.02  ------ General
% 2.00/1.02  
% 2.00/1.02  abstr_ref_over_cycles:                  0
% 2.00/1.02  abstr_ref_under_cycles:                 0
% 2.00/1.02  gc_basic_clause_elim:                   0
% 2.00/1.02  forced_gc_time:                         0
% 2.00/1.02  parsing_time:                           0.014
% 2.00/1.02  unif_index_cands_time:                  0.
% 2.00/1.02  unif_index_add_time:                    0.
% 2.00/1.02  orderings_time:                         0.
% 2.00/1.02  out_proof_time:                         0.01
% 2.00/1.02  total_time:                             0.193
% 2.00/1.02  num_of_symbols:                         55
% 2.00/1.02  num_of_terms:                           3316
% 2.00/1.02  
% 2.00/1.02  ------ Preprocessing
% 2.00/1.02  
% 2.00/1.02  num_of_splits:                          0
% 2.00/1.02  num_of_split_atoms:                     0
% 2.00/1.02  num_of_reused_defs:                     0
% 2.00/1.02  num_eq_ax_congr_red:                    20
% 2.00/1.02  num_of_sem_filtered_clauses:            1
% 2.00/1.02  num_of_subtypes:                        0
% 2.00/1.02  monotx_restored_types:                  0
% 2.00/1.02  sat_num_of_epr_types:                   0
% 2.00/1.02  sat_num_of_non_cyclic_types:            0
% 2.00/1.02  sat_guarded_non_collapsed_types:        0
% 2.00/1.02  num_pure_diseq_elim:                    0
% 2.00/1.02  simp_replaced_by:                       0
% 2.00/1.02  res_preprocessed:                       108
% 2.00/1.02  prep_upred:                             0
% 2.00/1.02  prep_unflattend:                        51
% 2.00/1.02  smt_new_axioms:                         0
% 2.00/1.02  pred_elim_cands:                        6
% 2.00/1.02  pred_elim:                              8
% 2.00/1.02  pred_elim_cl:                           9
% 2.00/1.02  pred_elim_cycles:                       12
% 2.00/1.02  merged_defs:                            2
% 2.00/1.02  merged_defs_ncl:                        0
% 2.00/1.02  bin_hyper_res:                          2
% 2.00/1.02  prep_cycles:                            4
% 2.00/1.02  pred_elim_time:                         0.022
% 2.00/1.02  splitting_time:                         0.
% 2.00/1.02  sem_filter_time:                        0.
% 2.00/1.02  monotx_time:                            0.001
% 2.00/1.02  subtype_inf_time:                       0.
% 2.00/1.02  
% 2.00/1.02  ------ Problem properties
% 2.00/1.02  
% 2.00/1.02  clauses:                                20
% 2.00/1.02  conjectures:                            2
% 2.00/1.02  epr:                                    11
% 2.00/1.02  horn:                                   16
% 2.00/1.02  ground:                                 5
% 2.00/1.02  unary:                                  5
% 2.00/1.02  binary:                                 6
% 2.00/1.02  lits:                                   49
% 2.00/1.02  lits_eq:                                7
% 2.00/1.02  fd_pure:                                0
% 2.00/1.02  fd_pseudo:                              0
% 2.00/1.02  fd_cond:                                1
% 2.00/1.02  fd_pseudo_cond:                         3
% 2.00/1.02  ac_symbols:                             0
% 2.00/1.02  
% 2.00/1.02  ------ Propositional Solver
% 2.00/1.02  
% 2.00/1.02  prop_solver_calls:                      28
% 2.00/1.02  prop_fast_solver_calls:                 977
% 2.00/1.02  smt_solver_calls:                       0
% 2.00/1.02  smt_fast_solver_calls:                  0
% 2.00/1.02  prop_num_of_clauses:                    1739
% 2.00/1.02  prop_preprocess_simplified:             4892
% 2.00/1.02  prop_fo_subsumed:                       33
% 2.00/1.02  prop_solver_time:                       0.
% 2.00/1.02  smt_solver_time:                        0.
% 2.00/1.02  smt_fast_solver_time:                   0.
% 2.00/1.02  prop_fast_solver_time:                  0.
% 2.00/1.02  prop_unsat_core_time:                   0.
% 2.00/1.02  
% 2.00/1.02  ------ QBF
% 2.00/1.02  
% 2.00/1.02  qbf_q_res:                              0
% 2.00/1.02  qbf_num_tautologies:                    0
% 2.00/1.02  qbf_prep_cycles:                        0
% 2.00/1.02  
% 2.00/1.02  ------ BMC1
% 2.00/1.02  
% 2.00/1.02  bmc1_current_bound:                     -1
% 2.00/1.02  bmc1_last_solved_bound:                 -1
% 2.00/1.02  bmc1_unsat_core_size:                   -1
% 2.00/1.02  bmc1_unsat_core_parents_size:           -1
% 2.00/1.02  bmc1_merge_next_fun:                    0
% 2.00/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.02  
% 2.00/1.02  ------ Instantiation
% 2.00/1.02  
% 2.00/1.02  inst_num_of_clauses:                    502
% 2.00/1.02  inst_num_in_passive:                    175
% 2.00/1.02  inst_num_in_active:                     283
% 2.00/1.02  inst_num_in_unprocessed:                45
% 2.00/1.02  inst_num_of_loops:                      300
% 2.00/1.02  inst_num_of_learning_restarts:          0
% 2.00/1.02  inst_num_moves_active_passive:          13
% 2.00/1.02  inst_lit_activity:                      0
% 2.00/1.02  inst_lit_activity_moves:                0
% 2.00/1.02  inst_num_tautologies:                   0
% 2.00/1.02  inst_num_prop_implied:                  0
% 2.00/1.02  inst_num_existing_simplified:           0
% 2.00/1.02  inst_num_eq_res_simplified:             0
% 2.00/1.02  inst_num_child_elim:                    0
% 2.00/1.02  inst_num_of_dismatching_blockings:      149
% 2.00/1.02  inst_num_of_non_proper_insts:           445
% 2.00/1.02  inst_num_of_duplicates:                 0
% 2.00/1.02  inst_inst_num_from_inst_to_res:         0
% 2.00/1.02  inst_dismatching_checking_time:         0.
% 2.00/1.02  
% 2.00/1.02  ------ Resolution
% 2.00/1.02  
% 2.00/1.02  res_num_of_clauses:                     0
% 2.00/1.02  res_num_in_passive:                     0
% 2.00/1.02  res_num_in_active:                      0
% 2.00/1.02  res_num_of_loops:                       112
% 2.00/1.02  res_forward_subset_subsumed:            42
% 2.00/1.02  res_backward_subset_subsumed:           2
% 2.00/1.02  res_forward_subsumed:                   0
% 2.00/1.02  res_backward_subsumed:                  0
% 2.00/1.02  res_forward_subsumption_resolution:     0
% 2.00/1.02  res_backward_subsumption_resolution:    0
% 2.00/1.02  res_clause_to_clause_subsumption:       234
% 2.00/1.02  res_orphan_elimination:                 0
% 2.00/1.02  res_tautology_del:                      37
% 2.00/1.02  res_num_eq_res_simplified:              4
% 2.00/1.02  res_num_sel_changes:                    0
% 2.00/1.02  res_moves_from_active_to_pass:          0
% 2.00/1.02  
% 2.00/1.02  ------ Superposition
% 2.00/1.02  
% 2.00/1.02  sup_time_total:                         0.
% 2.00/1.02  sup_time_generating:                    0.
% 2.00/1.02  sup_time_sim_full:                      0.
% 2.00/1.02  sup_time_sim_immed:                     0.
% 2.00/1.02  
% 2.00/1.02  sup_num_of_clauses:                     46
% 2.00/1.02  sup_num_in_active:                      30
% 2.00/1.02  sup_num_in_passive:                     16
% 2.00/1.02  sup_num_of_loops:                       59
% 2.00/1.02  sup_fw_superposition:                   38
% 2.00/1.02  sup_bw_superposition:                   31
% 2.00/1.02  sup_immediate_simplified:               8
% 2.00/1.02  sup_given_eliminated:                   0
% 2.00/1.02  comparisons_done:                       0
% 2.00/1.02  comparisons_avoided:                    0
% 2.00/1.02  
% 2.00/1.02  ------ Simplifications
% 2.00/1.02  
% 2.00/1.02  
% 2.00/1.02  sim_fw_subset_subsumed:                 4
% 2.00/1.02  sim_bw_subset_subsumed:                 11
% 2.00/1.02  sim_fw_subsumed:                        1
% 2.00/1.02  sim_bw_subsumed:                        0
% 2.00/1.02  sim_fw_subsumption_res:                 3
% 2.00/1.02  sim_bw_subsumption_res:                 0
% 2.00/1.02  sim_tautology_del:                      3
% 2.00/1.02  sim_eq_tautology_del:                   4
% 2.00/1.02  sim_eq_res_simp:                        0
% 2.00/1.02  sim_fw_demodulated:                     0
% 2.00/1.02  sim_bw_demodulated:                     29
% 2.00/1.02  sim_light_normalised:                   1
% 2.00/1.02  sim_joinable_taut:                      0
% 2.00/1.02  sim_joinable_simp:                      0
% 2.00/1.02  sim_ac_normalised:                      0
% 2.00/1.02  sim_smt_subsumption:                    0
% 2.00/1.02  
%------------------------------------------------------------------------------
