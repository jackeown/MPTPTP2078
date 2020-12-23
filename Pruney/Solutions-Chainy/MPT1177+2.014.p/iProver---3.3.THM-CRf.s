%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:49 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  209 (3832 expanded)
%              Number of clauses        :  135 ( 690 expanded)
%              Number of leaves         :   19 (1259 expanded)
%              Depth                    :   26
%              Number of atoms          : 1027 (37126 expanded)
%              Number of equality atoms :  210 ( 734 expanded)
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f40])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44,f43,f42])).

fof(f74,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
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
    inference(pure_predicate_removal,[],[f10])).

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
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f39])).

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
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,negated_conjecture,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_206,plain,
    ( r2_xboole_0(sK2,sK3)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_207,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_464,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK3 != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_207])).

cnf(c_465,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1271,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_22,negated_conjecture,
    ( m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_454,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_207])).

cnf(c_455,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_456,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_466,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_13,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_595,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_596,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_646,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_596,c_24])).

cnf(c_647,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_651,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_28,c_27,c_26,c_25])).

cnf(c_876,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_651])).

cnf(c_1404,plain,
    ( ~ m2_orders_2(sK2,sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1405,plain,
    ( m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1680,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2150,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_2151,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2150])).

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
    inference(cnf_transformation,[],[f65])).

cnf(c_556,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_557,plain,
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
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_667,plain,
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
    inference(resolution_lifted,[status(thm)],[c_557,c_24])).

cnf(c_668,plain,
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
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_672,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_28,c_27,c_26,c_25])).

cnf(c_872,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | m1_orders_2(X1,sK0,X0)
    | m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_672])).

cnf(c_1681,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | m1_orders_2(X0,sK0,sK3)
    | m1_orders_2(sK3,sK0,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_2177,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_2178,plain,
    ( sK2 = sK3
    | m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m2_orders_2(sK2,sK0,sK1) != iProver_top
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2177])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_775,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_776,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_778,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_28,c_27,c_26,c_25])).

cnf(c_2674,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_2675,plain,
    ( m1_orders_2(sK3,sK0,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_3055,plain,
    ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1271,c_35,c_36,c_456,c_466,c_1405,c_2151,c_2178,c_2675])).

cnf(c_1274,plain,
    ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1275,plain,
    ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1265,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) = iProver_top
    | m1_orders_2(X1,sK0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_1788,plain,
    ( sK3 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,sK3) = iProver_top
    | m1_orders_2(sK3,sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1265])).

cnf(c_2070,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top
    | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1788])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_204,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_205,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_441,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_205])).

cnf(c_442,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_443,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1401,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1402,plain,
    ( m2_orders_2(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_1412,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1413,plain,
    ( m1_orders_2(sK2,sK0,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_2079,plain,
    ( m1_orders_2(sK3,sK0,sK2) = iProver_top
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_36,c_443,c_1402,c_1413])).

cnf(c_2080,plain,
    ( sK3 = sK2
    | m1_orders_2(sK3,sK0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2079])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_517,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_518,plain,
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
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_697,plain,
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
    inference(resolution_lifted,[status(thm)],[c_518,c_24])).

cnf(c_698,plain,
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
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_28,c_27,c_26,c_25])).

cnf(c_868,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m2_orders_2(X1,sK0,sK1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_orders_2(X0,sK0,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_702])).

cnf(c_1266,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK0,sK1) != iProver_top
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_78,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_780,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_1264,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_792,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_793,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_795,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_28,c_27,c_26,c_25])).

cnf(c_1268,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1590,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1268])).

cnf(c_1269,plain,
    ( m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_1591,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1269])).

cnf(c_2379,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_78,c_780,c_1590,c_1591])).

cnf(c_2380,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2379])).

cnf(c_2388,plain,
    ( sK2 = X0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_2380])).

cnf(c_2690,plain,
    ( sK3 = sK2
    | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_2388])).

cnf(c_2843,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_35,c_36,c_443,c_456,c_466,c_1402,c_1405,c_1413,c_2151,c_2178,c_2675])).

cnf(c_3059,plain,
    ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3055,c_2843])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_156,plain,
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

cnf(c_157,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_156])).

cnf(c_751,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_157,c_24])).

cnf(c_752,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_756,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_28,c_27,c_26,c_25])).

cnf(c_757,plain,
    ( ~ m1_orders_2(X0,sK0,X1)
    | ~ m1_orders_2(X1,sK0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_756])).

cnf(c_1270,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK0,X0) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1589,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_orders_2(X0,sK0,X1) != iProver_top
    | m1_orders_2(X1,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1270])).

cnf(c_3305,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(X0,sK0,sK2) != iProver_top
    | m1_orders_2(sK2,sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1589])).

cnf(c_3393,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_3305])).

cnf(c_3396,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_3059])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1276,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1276,c_9])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_360,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_361,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k1_xboole_0)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_11])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_16,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_394,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X4,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 != X3
    | k1_funct_1(X2,u1_struct_0(X1)) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_376,c_16])).

cnf(c_395,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_484,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_395,c_23])).

cnf(c_485,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_727,plain,
    ( ~ m2_orders_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_485,c_24])).

cnf(c_728,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0)
    | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_28,c_27,c_26,c_25])).

cnf(c_864,plain,
    ( ~ m2_orders_2(X0,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_732])).

cnf(c_1267,plain,
    ( m2_orders_2(X0,sK0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_2237,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1267])).

cnf(c_2561,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_2237])).

cnf(c_3404,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3396,c_2561])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1434,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1436,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3404,c_1436])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.18/0.92  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/0.92  
% 2.18/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/0.92  
% 2.18/0.92  ------  iProver source info
% 2.18/0.92  
% 2.18/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.18/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/0.92  git: non_committed_changes: false
% 2.18/0.92  git: last_make_outside_of_git: false
% 2.18/0.92  
% 2.18/0.92  ------ 
% 2.18/0.92  
% 2.18/0.92  ------ Input Options
% 2.18/0.92  
% 2.18/0.92  --out_options                           all
% 2.18/0.92  --tptp_safe_out                         true
% 2.18/0.92  --problem_path                          ""
% 2.18/0.92  --include_path                          ""
% 2.18/0.92  --clausifier                            res/vclausify_rel
% 2.18/0.92  --clausifier_options                    --mode clausify
% 2.18/0.92  --stdin                                 false
% 2.18/0.92  --stats_out                             all
% 2.18/0.92  
% 2.18/0.92  ------ General Options
% 2.18/0.92  
% 2.18/0.92  --fof                                   false
% 2.18/0.92  --time_out_real                         305.
% 2.18/0.92  --time_out_virtual                      -1.
% 2.18/0.92  --symbol_type_check                     false
% 2.18/0.92  --clausify_out                          false
% 2.18/0.92  --sig_cnt_out                           false
% 2.18/0.92  --trig_cnt_out                          false
% 2.18/0.92  --trig_cnt_out_tolerance                1.
% 2.18/0.92  --trig_cnt_out_sk_spl                   false
% 2.18/0.92  --abstr_cl_out                          false
% 2.18/0.92  
% 2.18/0.92  ------ Global Options
% 2.18/0.92  
% 2.18/0.92  --schedule                              default
% 2.18/0.92  --add_important_lit                     false
% 2.18/0.92  --prop_solver_per_cl                    1000
% 2.18/0.92  --min_unsat_core                        false
% 2.18/0.92  --soft_assumptions                      false
% 2.18/0.92  --soft_lemma_size                       3
% 2.18/0.92  --prop_impl_unit_size                   0
% 2.18/0.92  --prop_impl_unit                        []
% 2.18/0.92  --share_sel_clauses                     true
% 2.18/0.92  --reset_solvers                         false
% 2.18/0.92  --bc_imp_inh                            [conj_cone]
% 2.18/0.92  --conj_cone_tolerance                   3.
% 2.18/0.92  --extra_neg_conj                        none
% 2.18/0.92  --large_theory_mode                     true
% 2.18/0.92  --prolific_symb_bound                   200
% 2.18/0.92  --lt_threshold                          2000
% 2.18/0.92  --clause_weak_htbl                      true
% 2.18/0.92  --gc_record_bc_elim                     false
% 2.18/0.92  
% 2.18/0.92  ------ Preprocessing Options
% 2.18/0.92  
% 2.18/0.92  --preprocessing_flag                    true
% 2.18/0.92  --time_out_prep_mult                    0.1
% 2.18/0.92  --splitting_mode                        input
% 2.18/0.92  --splitting_grd                         true
% 2.18/0.92  --splitting_cvd                         false
% 2.18/0.92  --splitting_cvd_svl                     false
% 2.18/0.92  --splitting_nvd                         32
% 2.18/0.92  --sub_typing                            true
% 2.18/0.92  --prep_gs_sim                           true
% 2.18/0.92  --prep_unflatten                        true
% 2.18/0.92  --prep_res_sim                          true
% 2.18/0.92  --prep_upred                            true
% 2.18/0.92  --prep_sem_filter                       exhaustive
% 2.18/0.92  --prep_sem_filter_out                   false
% 2.18/0.92  --pred_elim                             true
% 2.18/0.92  --res_sim_input                         true
% 2.18/0.92  --eq_ax_congr_red                       true
% 2.18/0.92  --pure_diseq_elim                       true
% 2.18/0.92  --brand_transform                       false
% 2.18/0.92  --non_eq_to_eq                          false
% 2.18/0.92  --prep_def_merge                        true
% 2.18/0.92  --prep_def_merge_prop_impl              false
% 2.18/0.92  --prep_def_merge_mbd                    true
% 2.18/0.92  --prep_def_merge_tr_red                 false
% 2.18/0.92  --prep_def_merge_tr_cl                  false
% 2.18/0.92  --smt_preprocessing                     true
% 2.18/0.92  --smt_ac_axioms                         fast
% 2.18/0.92  --preprocessed_out                      false
% 2.18/0.92  --preprocessed_stats                    false
% 2.18/0.92  
% 2.18/0.92  ------ Abstraction refinement Options
% 2.18/0.92  
% 2.18/0.92  --abstr_ref                             []
% 2.18/0.92  --abstr_ref_prep                        false
% 2.18/0.92  --abstr_ref_until_sat                   false
% 2.18/0.92  --abstr_ref_sig_restrict                funpre
% 2.18/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.92  --abstr_ref_under                       []
% 2.18/0.92  
% 2.18/0.92  ------ SAT Options
% 2.18/0.92  
% 2.18/0.92  --sat_mode                              false
% 2.18/0.92  --sat_fm_restart_options                ""
% 2.18/0.92  --sat_gr_def                            false
% 2.18/0.92  --sat_epr_types                         true
% 2.18/0.92  --sat_non_cyclic_types                  false
% 2.18/0.92  --sat_finite_models                     false
% 2.18/0.92  --sat_fm_lemmas                         false
% 2.18/0.92  --sat_fm_prep                           false
% 2.18/0.92  --sat_fm_uc_incr                        true
% 2.18/0.92  --sat_out_model                         small
% 2.18/0.92  --sat_out_clauses                       false
% 2.18/0.92  
% 2.18/0.92  ------ QBF Options
% 2.18/0.92  
% 2.18/0.92  --qbf_mode                              false
% 2.18/0.92  --qbf_elim_univ                         false
% 2.18/0.92  --qbf_dom_inst                          none
% 2.18/0.92  --qbf_dom_pre_inst                      false
% 2.18/0.92  --qbf_sk_in                             false
% 2.18/0.92  --qbf_pred_elim                         true
% 2.18/0.92  --qbf_split                             512
% 2.18/0.92  
% 2.18/0.92  ------ BMC1 Options
% 2.18/0.92  
% 2.18/0.92  --bmc1_incremental                      false
% 2.18/0.92  --bmc1_axioms                           reachable_all
% 2.18/0.92  --bmc1_min_bound                        0
% 2.18/0.92  --bmc1_max_bound                        -1
% 2.18/0.92  --bmc1_max_bound_default                -1
% 2.18/0.92  --bmc1_symbol_reachability              true
% 2.18/0.92  --bmc1_property_lemmas                  false
% 2.18/0.92  --bmc1_k_induction                      false
% 2.18/0.92  --bmc1_non_equiv_states                 false
% 2.18/0.92  --bmc1_deadlock                         false
% 2.18/0.92  --bmc1_ucm                              false
% 2.18/0.92  --bmc1_add_unsat_core                   none
% 2.18/0.92  --bmc1_unsat_core_children              false
% 2.18/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.92  --bmc1_out_stat                         full
% 2.18/0.92  --bmc1_ground_init                      false
% 2.18/0.92  --bmc1_pre_inst_next_state              false
% 2.18/0.92  --bmc1_pre_inst_state                   false
% 2.18/0.92  --bmc1_pre_inst_reach_state             false
% 2.18/0.92  --bmc1_out_unsat_core                   false
% 2.18/0.92  --bmc1_aig_witness_out                  false
% 2.18/0.92  --bmc1_verbose                          false
% 2.18/0.92  --bmc1_dump_clauses_tptp                false
% 2.18/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.92  --bmc1_dump_file                        -
% 2.18/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.92  --bmc1_ucm_extend_mode                  1
% 2.18/0.92  --bmc1_ucm_init_mode                    2
% 2.18/0.92  --bmc1_ucm_cone_mode                    none
% 2.18/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.92  --bmc1_ucm_relax_model                  4
% 2.18/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.92  --bmc1_ucm_layered_model                none
% 2.18/0.92  --bmc1_ucm_max_lemma_size               10
% 2.18/0.92  
% 2.18/0.92  ------ AIG Options
% 2.18/0.92  
% 2.18/0.92  --aig_mode                              false
% 2.18/0.92  
% 2.18/0.92  ------ Instantiation Options
% 2.18/0.92  
% 2.18/0.92  --instantiation_flag                    true
% 2.18/0.92  --inst_sos_flag                         false
% 2.18/0.92  --inst_sos_phase                        true
% 2.18/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.92  --inst_lit_sel_side                     num_symb
% 2.18/0.92  --inst_solver_per_active                1400
% 2.18/0.92  --inst_solver_calls_frac                1.
% 2.18/0.92  --inst_passive_queue_type               priority_queues
% 2.18/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.92  --inst_passive_queues_freq              [25;2]
% 2.18/0.92  --inst_dismatching                      true
% 2.18/0.92  --inst_eager_unprocessed_to_passive     true
% 2.18/0.92  --inst_prop_sim_given                   true
% 2.18/0.92  --inst_prop_sim_new                     false
% 2.18/0.92  --inst_subs_new                         false
% 2.18/0.92  --inst_eq_res_simp                      false
% 2.18/0.92  --inst_subs_given                       false
% 2.18/0.92  --inst_orphan_elimination               true
% 2.18/0.92  --inst_learning_loop_flag               true
% 2.18/0.92  --inst_learning_start                   3000
% 2.18/0.92  --inst_learning_factor                  2
% 2.18/0.92  --inst_start_prop_sim_after_learn       3
% 2.18/0.92  --inst_sel_renew                        solver
% 2.18/0.92  --inst_lit_activity_flag                true
% 2.18/0.92  --inst_restr_to_given                   false
% 2.18/0.92  --inst_activity_threshold               500
% 2.18/0.92  --inst_out_proof                        true
% 2.18/0.92  
% 2.18/0.92  ------ Resolution Options
% 2.18/0.92  
% 2.18/0.92  --resolution_flag                       true
% 2.18/0.92  --res_lit_sel                           adaptive
% 2.18/0.92  --res_lit_sel_side                      none
% 2.18/0.92  --res_ordering                          kbo
% 2.18/0.92  --res_to_prop_solver                    active
% 2.18/0.92  --res_prop_simpl_new                    false
% 2.18/0.92  --res_prop_simpl_given                  true
% 2.18/0.92  --res_passive_queue_type                priority_queues
% 2.18/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.93  --res_passive_queues_freq               [15;5]
% 2.18/0.93  --res_forward_subs                      full
% 2.18/0.93  --res_backward_subs                     full
% 2.18/0.93  --res_forward_subs_resolution           true
% 2.18/0.93  --res_backward_subs_resolution          true
% 2.18/0.93  --res_orphan_elimination                true
% 2.18/0.93  --res_time_limit                        2.
% 2.18/0.93  --res_out_proof                         true
% 2.18/0.93  
% 2.18/0.93  ------ Superposition Options
% 2.18/0.93  
% 2.18/0.93  --superposition_flag                    true
% 2.18/0.93  --sup_passive_queue_type                priority_queues
% 2.18/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.93  --demod_completeness_check              fast
% 2.18/0.93  --demod_use_ground                      true
% 2.18/0.93  --sup_to_prop_solver                    passive
% 2.18/0.93  --sup_prop_simpl_new                    true
% 2.18/0.93  --sup_prop_simpl_given                  true
% 2.18/0.93  --sup_fun_splitting                     false
% 2.18/0.93  --sup_smt_interval                      50000
% 2.18/0.93  
% 2.18/0.93  ------ Superposition Simplification Setup
% 2.18/0.93  
% 2.18/0.93  --sup_indices_passive                   []
% 2.18/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_full_bw                           [BwDemod]
% 2.18/0.93  --sup_immed_triv                        [TrivRules]
% 2.18/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_immed_bw_main                     []
% 2.18/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.93  
% 2.18/0.93  ------ Combination Options
% 2.18/0.93  
% 2.18/0.93  --comb_res_mult                         3
% 2.18/0.93  --comb_sup_mult                         2
% 2.18/0.93  --comb_inst_mult                        10
% 2.18/0.93  
% 2.18/0.93  ------ Debug Options
% 2.18/0.93  
% 2.18/0.93  --dbg_backtrace                         false
% 2.18/0.93  --dbg_dump_prop_clauses                 false
% 2.18/0.93  --dbg_dump_prop_clauses_file            -
% 2.18/0.93  --dbg_out_stat                          false
% 2.18/0.93  ------ Parsing...
% 2.18/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/0.93  
% 2.18/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.18/0.93  
% 2.18/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/0.93  
% 2.18/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/0.93  ------ Proving...
% 2.18/0.93  ------ Problem Properties 
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  clauses                                 17
% 2.18/0.93  conjectures                             2
% 2.18/0.93  EPR                                     10
% 2.18/0.93  Horn                                    15
% 2.18/0.93  unary                                   6
% 2.18/0.93  binary                                  3
% 2.18/0.93  lits                                    41
% 2.18/0.93  lits eq                                 7
% 2.18/0.93  fd_pure                                 0
% 2.18/0.93  fd_pseudo                               0
% 2.18/0.93  fd_cond                                 1
% 2.18/0.93  fd_pseudo_cond                          3
% 2.18/0.93  AC symbols                              0
% 2.18/0.93  
% 2.18/0.93  ------ Schedule dynamic 5 is on 
% 2.18/0.93  
% 2.18/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  ------ 
% 2.18/0.93  Current options:
% 2.18/0.93  ------ 
% 2.18/0.93  
% 2.18/0.93  ------ Input Options
% 2.18/0.93  
% 2.18/0.93  --out_options                           all
% 2.18/0.93  --tptp_safe_out                         true
% 2.18/0.93  --problem_path                          ""
% 2.18/0.93  --include_path                          ""
% 2.18/0.93  --clausifier                            res/vclausify_rel
% 2.18/0.93  --clausifier_options                    --mode clausify
% 2.18/0.93  --stdin                                 false
% 2.18/0.93  --stats_out                             all
% 2.18/0.93  
% 2.18/0.93  ------ General Options
% 2.18/0.93  
% 2.18/0.93  --fof                                   false
% 2.18/0.93  --time_out_real                         305.
% 2.18/0.93  --time_out_virtual                      -1.
% 2.18/0.93  --symbol_type_check                     false
% 2.18/0.93  --clausify_out                          false
% 2.18/0.93  --sig_cnt_out                           false
% 2.18/0.93  --trig_cnt_out                          false
% 2.18/0.93  --trig_cnt_out_tolerance                1.
% 2.18/0.93  --trig_cnt_out_sk_spl                   false
% 2.18/0.93  --abstr_cl_out                          false
% 2.18/0.93  
% 2.18/0.93  ------ Global Options
% 2.18/0.93  
% 2.18/0.93  --schedule                              default
% 2.18/0.93  --add_important_lit                     false
% 2.18/0.93  --prop_solver_per_cl                    1000
% 2.18/0.93  --min_unsat_core                        false
% 2.18/0.93  --soft_assumptions                      false
% 2.18/0.93  --soft_lemma_size                       3
% 2.18/0.93  --prop_impl_unit_size                   0
% 2.18/0.93  --prop_impl_unit                        []
% 2.18/0.93  --share_sel_clauses                     true
% 2.18/0.93  --reset_solvers                         false
% 2.18/0.93  --bc_imp_inh                            [conj_cone]
% 2.18/0.93  --conj_cone_tolerance                   3.
% 2.18/0.93  --extra_neg_conj                        none
% 2.18/0.93  --large_theory_mode                     true
% 2.18/0.93  --prolific_symb_bound                   200
% 2.18/0.93  --lt_threshold                          2000
% 2.18/0.93  --clause_weak_htbl                      true
% 2.18/0.93  --gc_record_bc_elim                     false
% 2.18/0.93  
% 2.18/0.93  ------ Preprocessing Options
% 2.18/0.93  
% 2.18/0.93  --preprocessing_flag                    true
% 2.18/0.93  --time_out_prep_mult                    0.1
% 2.18/0.93  --splitting_mode                        input
% 2.18/0.93  --splitting_grd                         true
% 2.18/0.93  --splitting_cvd                         false
% 2.18/0.93  --splitting_cvd_svl                     false
% 2.18/0.93  --splitting_nvd                         32
% 2.18/0.93  --sub_typing                            true
% 2.18/0.93  --prep_gs_sim                           true
% 2.18/0.93  --prep_unflatten                        true
% 2.18/0.93  --prep_res_sim                          true
% 2.18/0.93  --prep_upred                            true
% 2.18/0.93  --prep_sem_filter                       exhaustive
% 2.18/0.93  --prep_sem_filter_out                   false
% 2.18/0.93  --pred_elim                             true
% 2.18/0.93  --res_sim_input                         true
% 2.18/0.93  --eq_ax_congr_red                       true
% 2.18/0.93  --pure_diseq_elim                       true
% 2.18/0.93  --brand_transform                       false
% 2.18/0.93  --non_eq_to_eq                          false
% 2.18/0.93  --prep_def_merge                        true
% 2.18/0.93  --prep_def_merge_prop_impl              false
% 2.18/0.93  --prep_def_merge_mbd                    true
% 2.18/0.93  --prep_def_merge_tr_red                 false
% 2.18/0.93  --prep_def_merge_tr_cl                  false
% 2.18/0.93  --smt_preprocessing                     true
% 2.18/0.93  --smt_ac_axioms                         fast
% 2.18/0.93  --preprocessed_out                      false
% 2.18/0.93  --preprocessed_stats                    false
% 2.18/0.93  
% 2.18/0.93  ------ Abstraction refinement Options
% 2.18/0.93  
% 2.18/0.93  --abstr_ref                             []
% 2.18/0.93  --abstr_ref_prep                        false
% 2.18/0.93  --abstr_ref_until_sat                   false
% 2.18/0.93  --abstr_ref_sig_restrict                funpre
% 2.18/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.93  --abstr_ref_under                       []
% 2.18/0.93  
% 2.18/0.93  ------ SAT Options
% 2.18/0.93  
% 2.18/0.93  --sat_mode                              false
% 2.18/0.93  --sat_fm_restart_options                ""
% 2.18/0.93  --sat_gr_def                            false
% 2.18/0.93  --sat_epr_types                         true
% 2.18/0.93  --sat_non_cyclic_types                  false
% 2.18/0.93  --sat_finite_models                     false
% 2.18/0.93  --sat_fm_lemmas                         false
% 2.18/0.93  --sat_fm_prep                           false
% 2.18/0.93  --sat_fm_uc_incr                        true
% 2.18/0.93  --sat_out_model                         small
% 2.18/0.93  --sat_out_clauses                       false
% 2.18/0.93  
% 2.18/0.93  ------ QBF Options
% 2.18/0.93  
% 2.18/0.93  --qbf_mode                              false
% 2.18/0.93  --qbf_elim_univ                         false
% 2.18/0.93  --qbf_dom_inst                          none
% 2.18/0.93  --qbf_dom_pre_inst                      false
% 2.18/0.93  --qbf_sk_in                             false
% 2.18/0.93  --qbf_pred_elim                         true
% 2.18/0.93  --qbf_split                             512
% 2.18/0.93  
% 2.18/0.93  ------ BMC1 Options
% 2.18/0.93  
% 2.18/0.93  --bmc1_incremental                      false
% 2.18/0.93  --bmc1_axioms                           reachable_all
% 2.18/0.93  --bmc1_min_bound                        0
% 2.18/0.93  --bmc1_max_bound                        -1
% 2.18/0.93  --bmc1_max_bound_default                -1
% 2.18/0.93  --bmc1_symbol_reachability              true
% 2.18/0.93  --bmc1_property_lemmas                  false
% 2.18/0.93  --bmc1_k_induction                      false
% 2.18/0.93  --bmc1_non_equiv_states                 false
% 2.18/0.93  --bmc1_deadlock                         false
% 2.18/0.93  --bmc1_ucm                              false
% 2.18/0.93  --bmc1_add_unsat_core                   none
% 2.18/0.93  --bmc1_unsat_core_children              false
% 2.18/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.93  --bmc1_out_stat                         full
% 2.18/0.93  --bmc1_ground_init                      false
% 2.18/0.93  --bmc1_pre_inst_next_state              false
% 2.18/0.93  --bmc1_pre_inst_state                   false
% 2.18/0.93  --bmc1_pre_inst_reach_state             false
% 2.18/0.93  --bmc1_out_unsat_core                   false
% 2.18/0.93  --bmc1_aig_witness_out                  false
% 2.18/0.93  --bmc1_verbose                          false
% 2.18/0.93  --bmc1_dump_clauses_tptp                false
% 2.18/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.93  --bmc1_dump_file                        -
% 2.18/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.93  --bmc1_ucm_extend_mode                  1
% 2.18/0.93  --bmc1_ucm_init_mode                    2
% 2.18/0.93  --bmc1_ucm_cone_mode                    none
% 2.18/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.93  --bmc1_ucm_relax_model                  4
% 2.18/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.93  --bmc1_ucm_layered_model                none
% 2.18/0.93  --bmc1_ucm_max_lemma_size               10
% 2.18/0.93  
% 2.18/0.93  ------ AIG Options
% 2.18/0.93  
% 2.18/0.93  --aig_mode                              false
% 2.18/0.93  
% 2.18/0.93  ------ Instantiation Options
% 2.18/0.93  
% 2.18/0.93  --instantiation_flag                    true
% 2.18/0.93  --inst_sos_flag                         false
% 2.18/0.93  --inst_sos_phase                        true
% 2.18/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.93  --inst_lit_sel_side                     none
% 2.18/0.93  --inst_solver_per_active                1400
% 2.18/0.93  --inst_solver_calls_frac                1.
% 2.18/0.93  --inst_passive_queue_type               priority_queues
% 2.18/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.93  --inst_passive_queues_freq              [25;2]
% 2.18/0.93  --inst_dismatching                      true
% 2.18/0.93  --inst_eager_unprocessed_to_passive     true
% 2.18/0.93  --inst_prop_sim_given                   true
% 2.18/0.93  --inst_prop_sim_new                     false
% 2.18/0.93  --inst_subs_new                         false
% 2.18/0.93  --inst_eq_res_simp                      false
% 2.18/0.93  --inst_subs_given                       false
% 2.18/0.93  --inst_orphan_elimination               true
% 2.18/0.93  --inst_learning_loop_flag               true
% 2.18/0.93  --inst_learning_start                   3000
% 2.18/0.93  --inst_learning_factor                  2
% 2.18/0.93  --inst_start_prop_sim_after_learn       3
% 2.18/0.93  --inst_sel_renew                        solver
% 2.18/0.93  --inst_lit_activity_flag                true
% 2.18/0.93  --inst_restr_to_given                   false
% 2.18/0.93  --inst_activity_threshold               500
% 2.18/0.93  --inst_out_proof                        true
% 2.18/0.93  
% 2.18/0.93  ------ Resolution Options
% 2.18/0.93  
% 2.18/0.93  --resolution_flag                       false
% 2.18/0.93  --res_lit_sel                           adaptive
% 2.18/0.93  --res_lit_sel_side                      none
% 2.18/0.93  --res_ordering                          kbo
% 2.18/0.93  --res_to_prop_solver                    active
% 2.18/0.93  --res_prop_simpl_new                    false
% 2.18/0.93  --res_prop_simpl_given                  true
% 2.18/0.93  --res_passive_queue_type                priority_queues
% 2.18/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.93  --res_passive_queues_freq               [15;5]
% 2.18/0.93  --res_forward_subs                      full
% 2.18/0.93  --res_backward_subs                     full
% 2.18/0.93  --res_forward_subs_resolution           true
% 2.18/0.93  --res_backward_subs_resolution          true
% 2.18/0.93  --res_orphan_elimination                true
% 2.18/0.93  --res_time_limit                        2.
% 2.18/0.93  --res_out_proof                         true
% 2.18/0.93  
% 2.18/0.93  ------ Superposition Options
% 2.18/0.93  
% 2.18/0.93  --superposition_flag                    true
% 2.18/0.93  --sup_passive_queue_type                priority_queues
% 2.18/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.93  --demod_completeness_check              fast
% 2.18/0.93  --demod_use_ground                      true
% 2.18/0.93  --sup_to_prop_solver                    passive
% 2.18/0.93  --sup_prop_simpl_new                    true
% 2.18/0.93  --sup_prop_simpl_given                  true
% 2.18/0.93  --sup_fun_splitting                     false
% 2.18/0.93  --sup_smt_interval                      50000
% 2.18/0.93  
% 2.18/0.93  ------ Superposition Simplification Setup
% 2.18/0.93  
% 2.18/0.93  --sup_indices_passive                   []
% 2.18/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_full_bw                           [BwDemod]
% 2.18/0.93  --sup_immed_triv                        [TrivRules]
% 2.18/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_immed_bw_main                     []
% 2.18/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.93  
% 2.18/0.93  ------ Combination Options
% 2.18/0.93  
% 2.18/0.93  --comb_res_mult                         3
% 2.18/0.93  --comb_sup_mult                         2
% 2.18/0.93  --comb_inst_mult                        10
% 2.18/0.93  
% 2.18/0.93  ------ Debug Options
% 2.18/0.93  
% 2.18/0.93  --dbg_backtrace                         false
% 2.18/0.93  --dbg_dump_prop_clauses                 false
% 2.18/0.93  --dbg_dump_prop_clauses_file            -
% 2.18/0.93  --dbg_out_stat                          false
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  ------ Proving...
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  % SZS status Theorem for theBenchmark.p
% 2.18/0.93  
% 2.18/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/0.93  
% 2.18/0.93  fof(f1,axiom,(
% 2.18/0.93    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f35,plain,(
% 2.18/0.93    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.18/0.93    inference(nnf_transformation,[],[f1])).
% 2.18/0.93  
% 2.18/0.93  fof(f36,plain,(
% 2.18/0.93    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.18/0.93    inference(flattening,[],[f35])).
% 2.18/0.93  
% 2.18/0.93  fof(f48,plain,(
% 2.18/0.93    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f36])).
% 2.18/0.93  
% 2.18/0.93  fof(f76,plain,(
% 2.18/0.93    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.18/0.93    inference(equality_resolution,[],[f48])).
% 2.18/0.93  
% 2.18/0.93  fof(f15,conjecture,(
% 2.18/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f16,negated_conjecture,(
% 2.18/0.93    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 2.18/0.93    inference(negated_conjecture,[],[f15])).
% 2.18/0.93  
% 2.18/0.93  fof(f33,plain,(
% 2.18/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f16])).
% 2.18/0.93  
% 2.18/0.93  fof(f34,plain,(
% 2.18/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f33])).
% 2.18/0.93  
% 2.18/0.93  fof(f40,plain,(
% 2.18/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.18/0.93    inference(nnf_transformation,[],[f34])).
% 2.18/0.93  
% 2.18/0.93  fof(f41,plain,(
% 2.18/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f40])).
% 2.18/0.93  
% 2.18/0.93  fof(f45,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK3) | ~r2_xboole_0(X2,sK3)) & (m1_orders_2(X2,X0,sK3) | r2_xboole_0(X2,sK3)) & m2_orders_2(sK3,X0,X1))) )),
% 2.18/0.93    introduced(choice_axiom,[])).
% 2.18/0.93  
% 2.18/0.93  fof(f44,plain,(
% 2.18/0.93    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK2,X0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,X0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK2,X0,X1))) )),
% 2.18/0.93    introduced(choice_axiom,[])).
% 2.18/0.93  
% 2.18/0.93  fof(f43,plain,(
% 2.18/0.93    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK1)) & m2_orders_2(X2,X0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))))) )),
% 2.18/0.93    introduced(choice_axiom,[])).
% 2.18/0.93  
% 2.18/0.93  fof(f42,plain,(
% 2.18/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.18/0.93    introduced(choice_axiom,[])).
% 2.18/0.93  
% 2.18/0.93  fof(f46,plain,(
% 2.18/0.93    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.18/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44,f43,f42])).
% 2.18/0.93  
% 2.18/0.93  fof(f74,plain,(
% 2.18/0.93    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f72,plain,(
% 2.18/0.93    m2_orders_2(sK2,sK0,sK1)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f73,plain,(
% 2.18/0.93    m2_orders_2(sK3,sK0,sK1)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f47,plain,(
% 2.18/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f36])).
% 2.18/0.93  
% 2.18/0.93  fof(f10,axiom,(
% 2.18/0.93    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f17,plain,(
% 2.18/0.93    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/0.93    inference(pure_predicate_removal,[],[f10])).
% 2.18/0.93  
% 2.18/0.93  fof(f23,plain,(
% 2.18/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f17])).
% 2.18/0.93  
% 2.18/0.93  fof(f24,plain,(
% 2.18/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f23])).
% 2.18/0.93  
% 2.18/0.93  fof(f60,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f24])).
% 2.18/0.93  
% 2.18/0.93  fof(f71,plain,(
% 2.18/0.93    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f70,plain,(
% 2.18/0.93    l1_orders_2(sK0)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f66,plain,(
% 2.18/0.93    ~v2_struct_0(sK0)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f67,plain,(
% 2.18/0.93    v3_orders_2(sK0)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f68,plain,(
% 2.18/0.93    v4_orders_2(sK0)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f69,plain,(
% 2.18/0.93    v5_orders_2(sK0)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f2,axiom,(
% 2.18/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f37,plain,(
% 2.18/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.93    inference(nnf_transformation,[],[f2])).
% 2.18/0.93  
% 2.18/0.93  fof(f38,plain,(
% 2.18/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.93    inference(flattening,[],[f37])).
% 2.18/0.93  
% 2.18/0.93  fof(f52,plain,(
% 2.18/0.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f38])).
% 2.18/0.93  
% 2.18/0.93  fof(f14,axiom,(
% 2.18/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f31,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f14])).
% 2.18/0.93  
% 2.18/0.93  fof(f32,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f31])).
% 2.18/0.93  
% 2.18/0.93  fof(f39,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(nnf_transformation,[],[f32])).
% 2.18/0.93  
% 2.18/0.93  fof(f65,plain,(
% 2.18/0.93    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f39])).
% 2.18/0.93  
% 2.18/0.93  fof(f11,axiom,(
% 2.18/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f25,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f11])).
% 2.18/0.93  
% 2.18/0.93  fof(f26,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f25])).
% 2.18/0.93  
% 2.18/0.93  fof(f61,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f26])).
% 2.18/0.93  
% 2.18/0.93  fof(f49,plain,(
% 2.18/0.93    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f36])).
% 2.18/0.93  
% 2.18/0.93  fof(f75,plain,(
% 2.18/0.93    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 2.18/0.93    inference(cnf_transformation,[],[f46])).
% 2.18/0.93  
% 2.18/0.93  fof(f64,plain,(
% 2.18/0.93    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f39])).
% 2.18/0.93  
% 2.18/0.93  fof(f9,axiom,(
% 2.18/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f21,plain,(
% 2.18/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f9])).
% 2.18/0.93  
% 2.18/0.93  fof(f22,plain,(
% 2.18/0.93    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f21])).
% 2.18/0.93  
% 2.18/0.93  fof(f59,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f22])).
% 2.18/0.93  
% 2.18/0.93  fof(f12,axiom,(
% 2.18/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f27,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f12])).
% 2.18/0.93  
% 2.18/0.93  fof(f28,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f27])).
% 2.18/0.93  
% 2.18/0.93  fof(f62,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f28])).
% 2.18/0.93  
% 2.18/0.93  fof(f7,axiom,(
% 2.18/0.93    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f57,plain,(
% 2.18/0.93    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.18/0.93    inference(cnf_transformation,[],[f7])).
% 2.18/0.93  
% 2.18/0.93  fof(f6,axiom,(
% 2.18/0.93    ! [X0] : k2_subset_1(X0) = X0),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f56,plain,(
% 2.18/0.93    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.18/0.93    inference(cnf_transformation,[],[f6])).
% 2.18/0.93  
% 2.18/0.93  fof(f4,axiom,(
% 2.18/0.93    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f54,plain,(
% 2.18/0.93    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f4])).
% 2.18/0.93  
% 2.18/0.93  fof(f5,axiom,(
% 2.18/0.93    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f18,plain,(
% 2.18/0.93    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.18/0.93    inference(ennf_transformation,[],[f5])).
% 2.18/0.93  
% 2.18/0.93  fof(f19,plain,(
% 2.18/0.93    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.18/0.93    inference(flattening,[],[f18])).
% 2.18/0.93  
% 2.18/0.93  fof(f55,plain,(
% 2.18/0.93    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f19])).
% 2.18/0.93  
% 2.18/0.93  fof(f8,axiom,(
% 2.18/0.93    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f20,plain,(
% 2.18/0.93    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.18/0.93    inference(ennf_transformation,[],[f8])).
% 2.18/0.93  
% 2.18/0.93  fof(f58,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f20])).
% 2.18/0.93  
% 2.18/0.93  fof(f13,axiom,(
% 2.18/0.93    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f29,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.18/0.93    inference(ennf_transformation,[],[f13])).
% 2.18/0.93  
% 2.18/0.93  fof(f30,plain,(
% 2.18/0.93    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.18/0.93    inference(flattening,[],[f29])).
% 2.18/0.93  
% 2.18/0.93  fof(f63,plain,(
% 2.18/0.93    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f30])).
% 2.18/0.93  
% 2.18/0.93  fof(f3,axiom,(
% 2.18/0.93    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/0.93  
% 2.18/0.93  fof(f53,plain,(
% 2.18/0.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.18/0.93    inference(cnf_transformation,[],[f3])).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1,plain,
% 2.18/0.93      ( ~ r2_xboole_0(X0,X0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f76]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_20,negated_conjecture,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.18/0.93      inference(cnf_transformation,[],[f74]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_206,plain,
% 2.18/0.93      ( r2_xboole_0(sK2,sK3) | m1_orders_2(sK2,sK0,sK3) ),
% 2.18/0.93      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_207,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3) ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_206]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_464,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) | sK3 != X0 | sK2 != X0 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_207]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_465,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) | sK2 != sK3 ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_464]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1271,plain,
% 2.18/0.93      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_22,negated_conjecture,
% 2.18/0.93      ( m2_orders_2(sK2,sK0,sK1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f72]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_35,plain,
% 2.18/0.93      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_21,negated_conjecture,
% 2.18/0.93      ( m2_orders_2(sK3,sK0,sK1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f73]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_36,plain,
% 2.18/0.93      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2,plain,
% 2.18/0.93      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f47]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_454,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3)
% 2.18/0.93      | r1_tarski(X0,X1)
% 2.18/0.93      | sK3 != X1
% 2.18/0.93      | sK2 != X0 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_207]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_455,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK2,sK3) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_454]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_456,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) = iProver_top
% 2.18/0.93      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_466,plain,
% 2.18/0.93      ( sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_13,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f60]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_23,negated_conjecture,
% 2.18/0.93      ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
% 2.18/0.93      inference(cnf_transformation,[],[f71]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_595,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK1 != X2 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_596,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_595]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_24,negated_conjecture,
% 2.18/0.93      ( l1_orders_2(sK0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f70]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_646,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_596,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_647,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0)
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_646]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_28,negated_conjecture,
% 2.18/0.93      ( ~ v2_struct_0(sK0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f66]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_27,negated_conjecture,
% 2.18/0.93      ( v3_orders_2(sK0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f67]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_26,negated_conjecture,
% 2.18/0.93      ( v4_orders_2(sK0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f68]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_25,negated_conjecture,
% 2.18/0.93      ( v5_orders_2(sK0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f69]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_651,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_647,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_876,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/0.93      inference(equality_resolution_simp,[status(thm)],[c_651]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1404,plain,
% 2.18/0.93      ( ~ m2_orders_2(sK2,sK0,sK1)
% 2.18/0.93      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_876]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1405,plain,
% 2.18/0.93      ( m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3,plain,
% 2.18/0.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.18/0.93      inference(cnf_transformation,[],[f52]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1680,plain,
% 2.18/0.93      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_3]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2150,plain,
% 2.18/0.93      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_1680]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2151,plain,
% 2.18/0.93      ( sK2 = sK3
% 2.18/0.93      | r1_tarski(sK3,sK2) != iProver_top
% 2.18/0.93      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_2150]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_17,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.18/0.93      | m1_orders_2(X3,X1,X0)
% 2.18/0.93      | m1_orders_2(X0,X1,X3)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X3 = X0 ),
% 2.18/0.93      inference(cnf_transformation,[],[f65]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_556,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.18/0.93      | m1_orders_2(X3,X1,X0)
% 2.18/0.93      | m1_orders_2(X0,X1,X3)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X3 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK1 != X2 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_557,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m2_orders_2(X2,X1,sK1)
% 2.18/0.93      | m1_orders_2(X2,X1,X0)
% 2.18/0.93      | m1_orders_2(X0,X1,X2)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X2 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_556]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_667,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m2_orders_2(X2,X1,sK1)
% 2.18/0.93      | m1_orders_2(X0,X1,X2)
% 2.18/0.93      | m1_orders_2(X2,X1,X0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | X2 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_557,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_668,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0)
% 2.18/0.93      | X1 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_667]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_672,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | X1 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_668,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_872,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | X1 = X0 ),
% 2.18/0.93      inference(equality_resolution_simp,[status(thm)],[c_672]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1681,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(sK3,sK0,sK1)
% 2.18/0.93      | m1_orders_2(X0,sK0,sK3)
% 2.18/0.93      | m1_orders_2(sK3,sK0,X0)
% 2.18/0.93      | X0 = sK3 ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_872]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2177,plain,
% 2.18/0.93      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(sK2,sK0,sK1)
% 2.18/0.93      | m1_orders_2(sK3,sK0,sK2)
% 2.18/0.93      | m1_orders_2(sK2,sK0,sK3)
% 2.18/0.93      | sK2 = sK3 ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_1681]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2178,plain,
% 2.18/0.93      ( sK2 = sK3
% 2.18/0.93      | m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.18/0.93      | m2_orders_2(sK2,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.18/0.93      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_2177]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_14,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | r1_tarski(X0,X2)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f61]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_775,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | r1_tarski(X0,X2)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_776,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | r1_tarski(X0,X1)
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_775]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_778,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | r1_tarski(X0,X1) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_776,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2674,plain,
% 2.18/0.93      ( ~ m1_orders_2(sK3,sK0,sK2)
% 2.18/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | r1_tarski(sK3,sK2) ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_778]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2675,plain,
% 2.18/0.93      ( m1_orders_2(sK3,sK0,sK2) != iProver_top
% 2.18/0.93      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/0.93      | r1_tarski(sK3,sK2) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3055,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_1271,c_35,c_36,c_456,c_466,c_1405,c_2151,c_2178,
% 2.18/0.93                 c_2675]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1274,plain,
% 2.18/0.93      ( m2_orders_2(sK2,sK0,sK1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1275,plain,
% 2.18/0.93      ( m2_orders_2(sK3,sK0,sK1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1265,plain,
% 2.18/0.93      ( X0 = X1
% 2.18/0.93      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) = iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1788,plain,
% 2.18/0.93      ( sK3 = X0
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,sK3) = iProver_top
% 2.18/0.93      | m1_orders_2(sK3,sK0,X0) = iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1275,c_1265]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2070,plain,
% 2.18/0.93      ( sK3 = sK2
% 2.18/0.93      | m1_orders_2(sK3,sK0,sK2) = iProver_top
% 2.18/0.93      | m1_orders_2(sK2,sK0,sK3) = iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1274,c_1788]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_0,plain,
% 2.18/0.93      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.18/0.93      inference(cnf_transformation,[],[f49]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_19,negated_conjecture,
% 2.18/0.93      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.18/0.93      inference(cnf_transformation,[],[f75]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_204,plain,
% 2.18/0.93      ( ~ r2_xboole_0(sK2,sK3) | ~ m1_orders_2(sK2,sK0,sK3) ),
% 2.18/0.93      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_205,plain,
% 2.18/0.93      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_204]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_441,plain,
% 2.18/0.93      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.18/0.93      | ~ r1_tarski(X0,X1)
% 2.18/0.93      | X1 = X0
% 2.18/0.93      | sK3 != X1
% 2.18/0.93      | sK2 != X0 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_205]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_442,plain,
% 2.18/0.93      ( ~ m1_orders_2(sK2,sK0,sK3) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_441]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_443,plain,
% 2.18/0.93      ( sK3 = sK2
% 2.18/0.93      | m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.18/0.93      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1401,plain,
% 2.18/0.93      ( ~ m2_orders_2(sK3,sK0,sK1)
% 2.18/0.93      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_876]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1402,plain,
% 2.18/0.93      ( m2_orders_2(sK3,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1412,plain,
% 2.18/0.93      ( ~ m1_orders_2(sK2,sK0,sK3)
% 2.18/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | r1_tarski(sK2,sK3) ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_778]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1413,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK3) != iProver_top
% 2.18/0.93      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/0.93      | r1_tarski(sK2,sK3) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2079,plain,
% 2.18/0.93      ( m1_orders_2(sK3,sK0,sK2) = iProver_top | sK3 = sK2 ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_2070,c_36,c_443,c_1402,c_1413]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2080,plain,
% 2.18/0.93      ( sK3 = sK2 | m1_orders_2(sK3,sK0,sK2) = iProver_top ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_2079]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_18,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X3,X1,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,X1,X3)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X3 = X0 ),
% 2.18/0.93      inference(cnf_transformation,[],[f64]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_517,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m2_orders_2(X3,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X3,X1,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,X1,X3)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X3 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK1 != X2 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_518,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m2_orders_2(X2,X1,sK1)
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X2 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_517]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_697,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m2_orders_2(X2,X1,sK1)
% 2.18/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | X2 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_518,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_698,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0)
% 2.18/0.93      | X1 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_697]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_702,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | X1 = X0
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_698,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_868,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m2_orders_2(X1,sK0,sK1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | X1 = X0 ),
% 2.18/0.93      inference(equality_resolution_simp,[status(thm)],[c_702]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1266,plain,
% 2.18/0.93      ( X0 = X1
% 2.18/0.93      | m2_orders_2(X1,sK0,sK1) != iProver_top
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_78,plain,
% 2.18/0.93      ( X0 = X1
% 2.18/0.93      | r1_tarski(X1,X0) != iProver_top
% 2.18/0.93      | r1_tarski(X0,X1) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_780,plain,
% 2.18/0.93      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1264,plain,
% 2.18/0.93      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_12,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f59]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_792,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_793,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_792]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_795,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_793,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1268,plain,
% 2.18/0.93      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1590,plain,
% 2.18/0.93      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.18/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1264,c_1268]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1269,plain,
% 2.18/0.93      ( m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1591,plain,
% 2.18/0.93      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.18/0.93      | r1_tarski(X1,X0) = iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1264,c_1269]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2379,plain,
% 2.18/0.93      ( X0 = X1
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) != iProver_top ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_1266,c_78,c_780,c_1590,c_1591]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2380,plain,
% 2.18/0.93      ( X0 = X1
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_2379]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2388,plain,
% 2.18/0.93      ( sK2 = X0
% 2.18/0.93      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.18/0.93      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1274,c_2380]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2690,plain,
% 2.18/0.93      ( sK3 = sK2 | m1_orders_2(sK2,sK0,sK3) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_2080,c_2388]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2843,plain,
% 2.18/0.93      ( sK3 = sK2 ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_2690,c_35,c_36,c_443,c_456,c_466,c_1402,c_1405,c_1413,
% 2.18/0.93                 c_2151,c_2178,c_2675]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3059,plain,
% 2.18/0.93      ( m1_orders_2(sK2,sK0,sK2) = iProver_top ),
% 2.18/0.93      inference(light_normalisation,[status(thm)],[c_3055,c_2843]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_15,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_xboole_0 = X2 ),
% 2.18/0.93      inference(cnf_transformation,[],[f62]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_156,plain,
% 2.18/0.93      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_xboole_0 = X2 ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_15,c_12]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_157,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_xboole_0 = X2 ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_156]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_751,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_2(X2,X1,X0)
% 2.18/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | sK0 != X1
% 2.18/0.93      | k1_xboole_0 = X2 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_157,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_752,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0)
% 2.18/0.93      | k1_xboole_0 = X0 ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_751]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_756,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | k1_xboole_0 = X0 ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_752,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_757,plain,
% 2.18/0.93      ( ~ m1_orders_2(X0,sK0,X1)
% 2.18/0.93      | ~ m1_orders_2(X1,sK0,X0)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/0.93      | k1_xboole_0 = X1 ),
% 2.18/0.93      inference(renaming,[status(thm)],[c_756]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1270,plain,
% 2.18/0.93      ( k1_xboole_0 = X0
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1589,plain,
% 2.18/0.93      ( k1_xboole_0 = X0
% 2.18/0.93      | m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_orders_2(X0,sK0,X1) != iProver_top
% 2.18/0.93      | m1_orders_2(X1,sK0,X0) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1264,c_1270]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3305,plain,
% 2.18/0.93      ( sK2 = k1_xboole_0
% 2.18/0.93      | m1_orders_2(X0,sK0,sK2) != iProver_top
% 2.18/0.93      | m1_orders_2(sK2,sK0,X0) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1274,c_1589]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3393,plain,
% 2.18/0.93      ( sK2 = k1_xboole_0 | m1_orders_2(sK2,sK0,sK2) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_3059,c_3305]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3396,plain,
% 2.18/0.93      ( sK2 = k1_xboole_0 ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_3393,c_3059]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_10,plain,
% 2.18/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.18/0.93      inference(cnf_transformation,[],[f57]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1276,plain,
% 2.18/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_9,plain,
% 2.18/0.93      ( k2_subset_1(X0) = X0 ),
% 2.18/0.93      inference(cnf_transformation,[],[f56]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1290,plain,
% 2.18/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.18/0.93      inference(light_normalisation,[status(thm)],[c_1276,c_9]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_7,plain,
% 2.18/0.93      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f54]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_8,plain,
% 2.18/0.93      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f55]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_360,plain,
% 2.18/0.93      ( ~ r1_tarski(X0,X1)
% 2.18/0.93      | v1_xboole_0(X0)
% 2.18/0.93      | X0 != X2
% 2.18/0.93      | k1_xboole_0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_361,plain,
% 2.18/0.93      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_360]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_11,plain,
% 2.18/0.93      ( ~ r2_hidden(X0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.18/0.93      | ~ v1_xboole_0(X2) ),
% 2.18/0.93      inference(cnf_transformation,[],[f58]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_375,plain,
% 2.18/0.93      ( ~ r2_hidden(X0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.18/0.93      | ~ r1_tarski(X3,k1_xboole_0)
% 2.18/0.93      | X2 != X3 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_361,c_11]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_376,plain,
% 2.18/0.93      ( ~ r2_hidden(X0,X1)
% 2.18/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.18/0.93      | ~ r1_tarski(X2,k1_xboole_0) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_375]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_16,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1) ),
% 2.18/0.93      inference(cnf_transformation,[],[f63]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_394,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.18/0.93      | ~ r1_tarski(X4,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | X0 != X3
% 2.18/0.93      | k1_funct_1(X2,u1_struct_0(X1)) != X5 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_376,c_16]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_395,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 2.18/0.93      | ~ r1_tarski(X3,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_394]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_484,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,X2)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 2.18/0.93      | ~ r1_tarski(X3,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK1 != X2 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_395,c_23]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_485,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.18/0.93      | ~ r1_tarski(X2,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | ~ l1_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_484]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_727,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,X1,sK1)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.18/0.93      | ~ r1_tarski(X2,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(X1)
% 2.18/0.93      | ~ v3_orders_2(X1)
% 2.18/0.93      | ~ v4_orders_2(X1)
% 2.18/0.93      | ~ v5_orders_2(X1)
% 2.18/0.93      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK0))
% 2.18/0.93      | sK0 != X1 ),
% 2.18/0.93      inference(resolution_lifted,[status(thm)],[c_485,c_24]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_728,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/0.93      | ~ r1_tarski(X1,k1_xboole_0)
% 2.18/0.93      | v2_struct_0(sK0)
% 2.18/0.93      | ~ v3_orders_2(sK0)
% 2.18/0.93      | ~ v4_orders_2(sK0)
% 2.18/0.93      | ~ v5_orders_2(sK0)
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(unflattening,[status(thm)],[c_727]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_732,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/0.93      | ~ r1_tarski(X1,k1_xboole_0)
% 2.18/0.93      | k1_orders_1(u1_struct_0(sK0)) != k1_orders_1(u1_struct_0(sK0)) ),
% 2.18/0.93      inference(global_propositional_subsumption,
% 2.18/0.93                [status(thm)],
% 2.18/0.93                [c_728,c_28,c_27,c_26,c_25]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_864,plain,
% 2.18/0.93      ( ~ m2_orders_2(X0,sK0,sK1)
% 2.18/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/0.93      | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.18/0.93      inference(equality_resolution_simp,[status(thm)],[c_732]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1267,plain,
% 2.18/0.93      ( m2_orders_2(X0,sK0,sK1) != iProver_top
% 2.18/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.18/0.93      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2237,plain,
% 2.18/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 2.18/0.93      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1274,c_1267]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_2561,plain,
% 2.18/0.93      ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.18/0.93      inference(superposition,[status(thm)],[c_1290,c_2237]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_3404,plain,
% 2.18/0.93      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.18/0.93      inference(demodulation,[status(thm)],[c_3396,c_2561]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_6,plain,
% 2.18/0.93      ( r1_tarski(k1_xboole_0,X0) ),
% 2.18/0.93      inference(cnf_transformation,[],[f53]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1434,plain,
% 2.18/0.93      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.18/0.93      inference(instantiation,[status(thm)],[c_6]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(c_1436,plain,
% 2.18/0.93      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.18/0.93      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 2.18/0.93  
% 2.18/0.93  cnf(contradiction,plain,
% 2.18/0.93      ( $false ),
% 2.18/0.93      inference(minisat,[status(thm)],[c_3404,c_1436]) ).
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/0.93  
% 2.18/0.93  ------                               Statistics
% 2.18/0.93  
% 2.18/0.93  ------ General
% 2.18/0.93  
% 2.18/0.93  abstr_ref_over_cycles:                  0
% 2.18/0.93  abstr_ref_under_cycles:                 0
% 2.18/0.93  gc_basic_clause_elim:                   0
% 2.18/0.93  forced_gc_time:                         0
% 2.18/0.93  parsing_time:                           0.012
% 2.18/0.93  unif_index_cands_time:                  0.
% 2.18/0.93  unif_index_add_time:                    0.
% 2.18/0.93  orderings_time:                         0.
% 2.18/0.93  out_proof_time:                         0.014
% 2.18/0.93  total_time:                             0.161
% 2.18/0.93  num_of_symbols:                         55
% 2.18/0.93  num_of_terms:                           2322
% 2.18/0.93  
% 2.18/0.93  ------ Preprocessing
% 2.18/0.93  
% 2.18/0.93  num_of_splits:                          0
% 2.18/0.93  num_of_split_atoms:                     0
% 2.18/0.93  num_of_reused_defs:                     0
% 2.18/0.93  num_eq_ax_congr_red:                    8
% 2.18/0.93  num_of_sem_filtered_clauses:            1
% 2.18/0.93  num_of_subtypes:                        0
% 2.18/0.93  monotx_restored_types:                  0
% 2.18/0.93  sat_num_of_epr_types:                   0
% 2.18/0.93  sat_num_of_non_cyclic_types:            0
% 2.18/0.93  sat_guarded_non_collapsed_types:        0
% 2.18/0.93  num_pure_diseq_elim:                    0
% 2.18/0.93  simp_replaced_by:                       0
% 2.18/0.93  res_preprocessed:                       96
% 2.18/0.93  prep_upred:                             0
% 2.18/0.93  prep_unflattend:                        23
% 2.18/0.93  smt_new_axioms:                         0
% 2.18/0.93  pred_elim_cands:                        4
% 2.18/0.93  pred_elim:                              10
% 2.18/0.93  pred_elim_cl:                           11
% 2.18/0.93  pred_elim_cycles:                       12
% 2.18/0.93  merged_defs:                            2
% 2.18/0.93  merged_defs_ncl:                        0
% 2.18/0.93  bin_hyper_res:                          2
% 2.18/0.93  prep_cycles:                            4
% 2.18/0.93  pred_elim_time:                         0.018
% 2.18/0.93  splitting_time:                         0.
% 2.18/0.93  sem_filter_time:                        0.
% 2.18/0.93  monotx_time:                            0.001
% 2.18/0.93  subtype_inf_time:                       0.
% 2.18/0.93  
% 2.18/0.93  ------ Problem properties
% 2.18/0.93  
% 2.18/0.93  clauses:                                17
% 2.18/0.93  conjectures:                            2
% 2.18/0.93  epr:                                    10
% 2.18/0.93  horn:                                   15
% 2.18/0.93  ground:                                 5
% 2.18/0.93  unary:                                  6
% 2.18/0.93  binary:                                 3
% 2.18/0.93  lits:                                   41
% 2.18/0.93  lits_eq:                                7
% 2.18/0.93  fd_pure:                                0
% 2.18/0.93  fd_pseudo:                              0
% 2.18/0.93  fd_cond:                                1
% 2.18/0.93  fd_pseudo_cond:                         3
% 2.18/0.93  ac_symbols:                             0
% 2.18/0.93  
% 2.18/0.93  ------ Propositional Solver
% 2.18/0.93  
% 2.18/0.93  prop_solver_calls:                      28
% 2.18/0.93  prop_fast_solver_calls:                 815
% 2.18/0.93  smt_solver_calls:                       0
% 2.18/0.93  smt_fast_solver_calls:                  0
% 2.18/0.93  prop_num_of_clauses:                    1145
% 2.18/0.93  prop_preprocess_simplified:             3753
% 2.18/0.93  prop_fo_subsumed:                       37
% 2.18/0.93  prop_solver_time:                       0.
% 2.18/0.93  smt_solver_time:                        0.
% 2.18/0.93  smt_fast_solver_time:                   0.
% 2.18/0.93  prop_fast_solver_time:                  0.
% 2.18/0.93  prop_unsat_core_time:                   0.
% 2.18/0.93  
% 2.18/0.93  ------ QBF
% 2.18/0.93  
% 2.18/0.93  qbf_q_res:                              0
% 2.18/0.93  qbf_num_tautologies:                    0
% 2.18/0.93  qbf_prep_cycles:                        0
% 2.18/0.93  
% 2.18/0.93  ------ BMC1
% 2.18/0.93  
% 2.18/0.93  bmc1_current_bound:                     -1
% 2.18/0.93  bmc1_last_solved_bound:                 -1
% 2.18/0.93  bmc1_unsat_core_size:                   -1
% 2.18/0.93  bmc1_unsat_core_parents_size:           -1
% 2.18/0.93  bmc1_merge_next_fun:                    0
% 2.18/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.18/0.93  
% 2.18/0.93  ------ Instantiation
% 2.18/0.93  
% 2.18/0.93  inst_num_of_clauses:                    312
% 2.18/0.93  inst_num_in_passive:                    49
% 2.18/0.93  inst_num_in_active:                     191
% 2.18/0.93  inst_num_in_unprocessed:                72
% 2.18/0.93  inst_num_of_loops:                      200
% 2.18/0.93  inst_num_of_learning_restarts:          0
% 2.18/0.93  inst_num_moves_active_passive:          6
% 2.18/0.93  inst_lit_activity:                      0
% 2.18/0.93  inst_lit_activity_moves:                0
% 2.18/0.93  inst_num_tautologies:                   0
% 2.18/0.93  inst_num_prop_implied:                  0
% 2.18/0.93  inst_num_existing_simplified:           0
% 2.18/0.93  inst_num_eq_res_simplified:             0
% 2.18/0.93  inst_num_child_elim:                    0
% 2.18/0.93  inst_num_of_dismatching_blockings:      116
% 2.18/0.93  inst_num_of_non_proper_insts:           293
% 2.18/0.93  inst_num_of_duplicates:                 0
% 2.18/0.93  inst_inst_num_from_inst_to_res:         0
% 2.18/0.93  inst_dismatching_checking_time:         0.
% 2.18/0.93  
% 2.18/0.93  ------ Resolution
% 2.18/0.93  
% 2.18/0.93  res_num_of_clauses:                     0
% 2.18/0.93  res_num_in_passive:                     0
% 2.18/0.93  res_num_in_active:                      0
% 2.18/0.93  res_num_of_loops:                       100
% 2.18/0.93  res_forward_subset_subsumed:            37
% 2.18/0.93  res_backward_subset_subsumed:           0
% 2.18/0.93  res_forward_subsumed:                   0
% 2.18/0.93  res_backward_subsumed:                  0
% 2.18/0.93  res_forward_subsumption_resolution:     0
% 2.18/0.93  res_backward_subsumption_resolution:    0
% 2.18/0.93  res_clause_to_clause_subsumption:       164
% 2.18/0.93  res_orphan_elimination:                 0
% 2.18/0.93  res_tautology_del:                      25
% 2.18/0.93  res_num_eq_res_simplified:              4
% 2.18/0.93  res_num_sel_changes:                    0
% 2.18/0.93  res_moves_from_active_to_pass:          0
% 2.18/0.93  
% 2.18/0.93  ------ Superposition
% 2.18/0.93  
% 2.18/0.93  sup_time_total:                         0.
% 2.18/0.93  sup_time_generating:                    0.
% 2.18/0.93  sup_time_sim_full:                      0.
% 2.18/0.93  sup_time_sim_immed:                     0.
% 2.18/0.93  
% 2.18/0.93  sup_num_of_clauses:                     29
% 2.18/0.93  sup_num_in_active:                      20
% 2.18/0.93  sup_num_in_passive:                     9
% 2.18/0.93  sup_num_of_loops:                       39
% 2.18/0.93  sup_fw_superposition:                   26
% 2.18/0.93  sup_bw_superposition:                   13
% 2.18/0.93  sup_immediate_simplified:               4
% 2.18/0.93  sup_given_eliminated:                   0
% 2.18/0.93  comparisons_done:                       0
% 2.18/0.93  comparisons_avoided:                    0
% 2.18/0.93  
% 2.18/0.93  ------ Simplifications
% 2.18/0.93  
% 2.18/0.93  
% 2.18/0.93  sim_fw_subset_subsumed:                 1
% 2.18/0.93  sim_bw_subset_subsumed:                 4
% 2.18/0.93  sim_fw_subsumed:                        3
% 2.18/0.93  sim_bw_subsumed:                        0
% 2.18/0.93  sim_fw_subsumption_res:                 0
% 2.18/0.93  sim_bw_subsumption_res:                 0
% 2.18/0.93  sim_tautology_del:                      0
% 2.18/0.93  sim_eq_tautology_del:                   5
% 2.18/0.93  sim_eq_res_simp:                        0
% 2.18/0.93  sim_fw_demodulated:                     0
% 2.18/0.93  sim_bw_demodulated:                     17
% 2.18/0.93  sim_light_normalised:                   3
% 2.18/0.93  sim_joinable_taut:                      0
% 2.18/0.93  sim_joinable_simp:                      0
% 2.18/0.93  sim_ac_normalised:                      0
% 2.18/0.93  sim_smt_subsumption:                    0
% 2.18/0.93  
%------------------------------------------------------------------------------
