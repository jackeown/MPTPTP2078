%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:56 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  176 (4870 expanded)
%              Number of clauses        :  111 ( 881 expanded)
%              Number of leaves         :   18 (1591 expanded)
%              Depth                    :   25
%              Number of atoms          : 1011 (46514 expanded)
%              Number of equality atoms :  171 (1247 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f40,f39,f38,f37])).

fof(f66,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,(
    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f64,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f68,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X3,X0,X2)
      | ~ m1_orders_2(X2,X0,X3)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1456,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2055,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1457,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2054,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_21,negated_conjecture,
    ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1455,negated_conjecture,
    ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2056,plain,
    ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_15,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_918,plain,
    ( m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
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
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_921,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_26,c_25,c_24,c_23])).

cnf(c_922,plain,
    ( m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_921])).

cnf(c_1448,plain,
    ( m1_orders_2(X0_57,sK1,X1_57)
    | m1_orders_2(X1_57,sK1,X0_57)
    | ~ m2_orders_2(X0_57,sK1,X0_59)
    | ~ m2_orders_2(X1_57,sK1,X0_59)
    | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0_57 = X1_57 ),
    inference(subtyping,[status(esa)],[c_922])).

cnf(c_2065,plain,
    ( X0_57 = X1_57
    | m1_orders_2(X0_57,sK1,X1_57) = iProver_top
    | m1_orders_2(X1_57,sK1,X0_57) = iProver_top
    | m2_orders_2(X1_57,sK1,X0_59) != iProver_top
    | m2_orders_2(X0_57,sK1,X0_59) != iProver_top
    | m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_2935,plain,
    ( X0_57 = X1_57
    | m1_orders_2(X1_57,sK1,X0_57) = iProver_top
    | m1_orders_2(X0_57,sK1,X1_57) = iProver_top
    | m2_orders_2(X1_57,sK1,sK2) != iProver_top
    | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2065])).

cnf(c_2986,plain,
    ( sK4 = X0_57
    | m1_orders_2(X0_57,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0_57) = iProver_top
    | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_2935])).

cnf(c_3016,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2986])).

cnf(c_17,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_992,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_993,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_995,plain,
    ( ~ m2_orders_2(X0,sK1,X1)
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_26,c_25,c_24,c_23])).

cnf(c_1445,plain,
    ( ~ m2_orders_2(X0_57,sK1,X0_59)
    | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_995])).

cnf(c_2255,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_1468,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_2405,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_18,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1458,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2053,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_16,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_892,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_893,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_895,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_26,c_25,c_24,c_23])).

cnf(c_896,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m2_orders_2(X0,sK1,X2)
    | ~ m2_orders_2(X1,sK1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_895])).

cnf(c_1449,plain,
    ( ~ m1_orders_2(X0_57,sK1,X1_57)
    | ~ m1_orders_2(X1_57,sK1,X0_57)
    | ~ m2_orders_2(X0_57,sK1,X0_59)
    | ~ m2_orders_2(X1_57,sK1,X0_59)
    | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | X0_57 = X1_57 ),
    inference(subtyping,[status(esa)],[c_896])).

cnf(c_2064,plain,
    ( X0_57 = X1_57
    | m1_orders_2(X0_57,sK1,X1_57) != iProver_top
    | m1_orders_2(X1_57,sK1,X0_57) != iProver_top
    | m2_orders_2(X1_57,sK1,X0_59) != iProver_top
    | m2_orders_2(X0_57,sK1,X0_59) != iProver_top
    | m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_2687,plain,
    ( X0_57 = X1_57
    | m1_orders_2(X1_57,sK1,X0_57) != iProver_top
    | m1_orders_2(X0_57,sK1,X1_57) != iProver_top
    | m2_orders_2(X1_57,sK1,sK2) != iProver_top
    | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2064])).

cnf(c_2740,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_2687])).

cnf(c_32,plain,
    ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_34,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_35,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_658,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(k1_xboole_0,X3,X4)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X3)),k9_setfam_1(u1_struct_0(X3)),k1_tarski(k1_xboole_0)))
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
    inference(resolution_lifted,[status(thm)],[c_12,c_10])).

cnf(c_659,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_683,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_659,c_11])).

cnf(c_767,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_683,c_22])).

cnf(c_768,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_772,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1)
    | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_26,c_25,c_24,c_23])).

cnf(c_1454,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0_59)
    | ~ m2_orders_2(k1_xboole_0,sK1,X1_59)
    | ~ m1_orders_1(X1_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(subtyping,[status(esa)],[c_772])).

cnf(c_1466,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1454])).

cnf(c_1465,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,X0_59)
    | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1454])).

cnf(c_1514,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK1,sK2)
    | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_2252,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_2253,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2252])).

cnf(c_1475,plain,
    ( ~ m2_orders_2(X0_57,X0_58,X0_59)
    | m2_orders_2(X1_57,X0_58,X0_59)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_2272,plain,
    ( m2_orders_2(X0_57,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X0_57 != sK4 ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_2274,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m2_orders_2(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_971,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_972,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_26,c_25,c_24,c_23])).

cnf(c_1446,plain,
    ( ~ m1_orders_2(X0_57,sK1,X1_57)
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_2294,plain,
    ( ~ m1_orders_2(X0_57,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_57,sK4) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_2429,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_2430,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1464,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | r2_xboole_0(X0_57,X1_57)
    | X1_57 = X0_57 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2388,plain,
    ( ~ r1_tarski(sK3,X0_57)
    | r2_xboole_0(sK3,X0_57)
    | X0_57 = sK3 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_2480,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_xboole_0(sK3,sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_2481,plain,
    ( sK4 = sK3
    | r1_tarski(sK3,sK4) != iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2480])).

cnf(c_1484,plain,
    ( ~ m1_orders_2(X0_57,X0_58,X1_57)
    | m1_orders_2(X2_57,X0_58,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    theory(equality)).

cnf(c_2282,plain,
    ( m1_orders_2(X0_57,sK1,X1_57)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X1_57 != sK4
    | X0_57 != sK3 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2404,plain,
    ( m1_orders_2(X0_57,sK1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X0_57 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_2534,plain,
    ( m1_orders_2(sK4,sK1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | sK4 != sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_2535,plain,
    ( sK4 != sK4
    | sK4 != sK3
    | m1_orders_2(sK4,sK1,sK4) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2534])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_944,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_945,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_26,c_25,c_24,c_23])).

cnf(c_1447,plain,
    ( ~ m1_orders_2(X0_57,sK1,X1_57)
    | ~ m1_orders_2(X1_57,sK1,X0_57)
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_57 ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_2334,plain,
    ( ~ m1_orders_2(X0_57,sK1,sK4)
    | ~ m1_orders_2(sK4,sK1,X0_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_2701,plain,
    ( ~ m1_orders_2(sK4,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2334])).

cnf(c_2705,plain,
    ( k1_xboole_0 = sK4
    | m1_orders_2(sK4,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2701])).

cnf(c_2743,plain,
    ( r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2740,c_21,c_32,c_19,c_34,c_35,c_1466,c_1514,c_2253,c_2274,c_2405,c_2430,c_2481,c_2535,c_2705])).

cnf(c_2745,plain,
    ( r2_xboole_0(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2743])).

cnf(c_3,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1461,plain,
    ( ~ r2_xboole_0(X0_57,X1_57)
    | ~ r2_xboole_0(X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2050,plain,
    ( r2_xboole_0(X0_57,X1_57) != iProver_top
    | r2_xboole_0(X1_57,X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_2748,plain,
    ( r2_xboole_0(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_2050])).

cnf(c_2754,plain,
    ( ~ r2_xboole_0(sK4,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2748])).

cnf(c_2304,plain,
    ( ~ m1_orders_2(X0_57,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0_57,sK3) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_2909,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_3023,plain,
    ( m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK4 = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3016])).

cnf(c_2573,plain,
    ( ~ r1_tarski(X0_57,sK3)
    | r2_xboole_0(X0_57,sK3)
    | sK3 = X0_57 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_3045,plain,
    ( ~ r1_tarski(sK4,sK3)
    | r2_xboole_0(sK4,sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2573])).

cnf(c_1473,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_2561,plain,
    ( X0_57 != X1_57
    | sK4 != X1_57
    | sK4 = X0_57 ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2780,plain,
    ( X0_57 != sK4
    | sK4 = X0_57
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_3084,plain,
    ( sK4 != sK4
    | sK4 = sK3
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_3111,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3016,c_21,c_20,c_17,c_2255,c_2405,c_2745,c_2754,c_2909,c_3023,c_3045,c_3084])).

cnf(c_3116,plain,
    ( r2_xboole_0(sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3111,c_2748])).

cnf(c_3118,plain,
    ( r2_xboole_0(sK3,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3111,c_2743])).

cnf(c_3133,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3116,c_3118])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.99  
% 1.70/0.99  ------  iProver source info
% 1.70/0.99  
% 1.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.99  git: non_committed_changes: false
% 1.70/0.99  git: last_make_outside_of_git: false
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    true
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     num_symb
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       true
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    passive
% 1.70/0.99  --sup_prop_simpl_new                    true
% 1.70/0.99  --sup_prop_simpl_given                  true
% 1.70/0.99  --sup_fun_splitting                     false
% 1.70/0.99  --sup_smt_interval                      50000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   []
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_full_bw                           [BwDemod]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         3
% 1.70/0.99  --comb_sup_mult                         2
% 1.70/0.99  --comb_inst_mult                        10
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  ------ Parsing...
% 1.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.70/0.99  ------ Proving...
% 1.70/0.99  ------ Problem Properties 
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  clauses                                 22
% 1.70/0.99  conjectures                             5
% 1.70/0.99  EPR                                     10
% 1.70/0.99  Horn                                    16
% 1.70/0.99  unary                                   5
% 1.70/0.99  binary                                  4
% 1.70/0.99  lits                                    71
% 1.70/0.99  lits eq                                 9
% 1.70/0.99  fd_pure                                 0
% 1.70/0.99  fd_pseudo                               0
% 1.70/0.99  fd_cond                                 4
% 1.70/0.99  fd_pseudo_cond                          3
% 1.70/0.99  AC symbols                              0
% 1.70/0.99  
% 1.70/0.99  ------ Schedule dynamic 5 is on 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  Current options:
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    true
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     none
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       false
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    passive
% 1.70/0.99  --sup_prop_simpl_new                    true
% 1.70/0.99  --sup_prop_simpl_given                  true
% 1.70/0.99  --sup_fun_splitting                     false
% 1.70/0.99  --sup_smt_interval                      50000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   []
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_full_bw                           [BwDemod]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         3
% 1.70/0.99  --comb_sup_mult                         2
% 1.70/0.99  --comb_inst_mult                        10
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ Proving...
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  % SZS status Theorem for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99   Resolution empty clause
% 1.70/0.99  
% 1.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  fof(f10,conjecture,(
% 1.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f11,negated_conjecture,(
% 1.70/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.70/0.99    inference(negated_conjecture,[],[f10])).
% 1.70/0.99  
% 1.70/0.99  fof(f25,plain,(
% 1.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f11])).
% 1.70/0.99  
% 1.70/0.99  fof(f26,plain,(
% 1.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f25])).
% 1.70/0.99  
% 1.70/0.99  fof(f35,plain,(
% 1.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.99    inference(nnf_transformation,[],[f26])).
% 1.70/0.99  
% 1.70/0.99  fof(f36,plain,(
% 1.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f35])).
% 1.70/0.99  
% 1.70/0.99  fof(f40,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f39,plain,(
% 1.70/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f38,plain,(
% 1.70/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f37,plain,(
% 1.70/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f41,plain,(
% 1.70/0.99    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f40,f39,f38,f37])).
% 1.70/0.99  
% 1.70/0.99  fof(f66,plain,(
% 1.70/0.99    m2_orders_2(sK3,sK1,sK2)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f67,plain,(
% 1.70/0.99    m2_orders_2(sK4,sK1,sK2)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f65,plain,(
% 1.70/0.99    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f5,axiom,(
% 1.70/0.99    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f53,plain,(
% 1.70/0.99    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f5])).
% 1.70/0.99  
% 1.70/0.99  fof(f80,plain,(
% 1.70/0.99    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))),
% 1.70/0.99    inference(definition_unfolding,[],[f65,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f9,axiom,(
% 1.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f23,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f9])).
% 1.70/0.99  
% 1.70/0.99  fof(f24,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f23])).
% 1.70/0.99  
% 1.70/0.99  fof(f34,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(nnf_transformation,[],[f24])).
% 1.70/0.99  
% 1.70/0.99  fof(f59,plain,(
% 1.70/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f34])).
% 1.70/0.99  
% 1.70/0.99  fof(f78,plain,(
% 1.70/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f59,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f64,plain,(
% 1.70/0.99    l1_orders_2(sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f60,plain,(
% 1.70/0.99    ~v2_struct_0(sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f61,plain,(
% 1.70/0.99    v3_orders_2(sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f62,plain,(
% 1.70/0.99    v4_orders_2(sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f63,plain,(
% 1.70/0.99    v5_orders_2(sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f69,plain,(
% 1.70/0.99    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f6,axiom,(
% 1.70/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f17,plain,(
% 1.70/0.99    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f6])).
% 1.70/0.99  
% 1.70/0.99  fof(f18,plain,(
% 1.70/0.99    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f17])).
% 1.70/0.99  
% 1.70/0.99  fof(f55,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f76,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f55,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f68,plain,(
% 1.70/0.99    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.70/0.99    inference(cnf_transformation,[],[f41])).
% 1.70/0.99  
% 1.70/0.99  fof(f58,plain,(
% 1.70/0.99    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f34])).
% 1.70/0.99  
% 1.70/0.99  fof(f79,plain,(
% 1.70/0.99    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f58,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f54,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f18])).
% 1.70/0.99  
% 1.70/0.99  fof(f77,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f54,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f4,axiom,(
% 1.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f15,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f4])).
% 1.70/0.99  
% 1.70/0.99  fof(f16,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f15])).
% 1.70/0.99  
% 1.70/0.99  fof(f29,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(nnf_transformation,[],[f16])).
% 1.70/0.99  
% 1.70/0.99  fof(f30,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f29])).
% 1.70/0.99  
% 1.70/0.99  fof(f31,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(rectify,[],[f30])).
% 1.70/0.99  
% 1.70/0.99  fof(f32,plain,(
% 1.70/0.99    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f33,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.70/0.99  
% 1.70/0.99  fof(f47,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f33])).
% 1.70/0.99  
% 1.70/0.99  fof(f75,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f47,f53])).
% 1.70/0.99  
% 1.70/0.99  fof(f82,plain,(
% 1.70/0.99    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(equality_resolution,[],[f75])).
% 1.70/0.99  
% 1.70/0.99  fof(f7,axiom,(
% 1.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f19,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f7])).
% 1.70/0.99  
% 1.70/0.99  fof(f20,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f19])).
% 1.70/0.99  
% 1.70/0.99  fof(f56,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f20])).
% 1.70/0.99  
% 1.70/0.99  fof(f1,axiom,(
% 1.70/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f27,plain,(
% 1.70/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.70/0.99    inference(nnf_transformation,[],[f1])).
% 1.70/0.99  
% 1.70/0.99  fof(f28,plain,(
% 1.70/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.70/0.99    inference(flattening,[],[f27])).
% 1.70/0.99  
% 1.70/0.99  fof(f44,plain,(
% 1.70/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f28])).
% 1.70/0.99  
% 1.70/0.99  fof(f8,axiom,(
% 1.70/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f21,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.70/0.99    inference(ennf_transformation,[],[f8])).
% 1.70/0.99  
% 1.70/0.99  fof(f22,plain,(
% 1.70/0.99    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.70/0.99    inference(flattening,[],[f21])).
% 1.70/0.99  
% 1.70/0.99  fof(f57,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f22])).
% 1.70/0.99  
% 1.70/0.99  fof(f2,axiom,(
% 1.70/0.99    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f12,plain,(
% 1.70/0.99    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 1.70/0.99    inference(ennf_transformation,[],[f2])).
% 1.70/0.99  
% 1.70/0.99  fof(f45,plain,(
% 1.70/0.99    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f12])).
% 1.70/0.99  
% 1.70/0.99  cnf(c_20,negated_conjecture,
% 1.70/0.99      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.70/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1456,negated_conjecture,
% 1.70/0.99      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2055,plain,
% 1.70/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_19,negated_conjecture,
% 1.70/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1457,negated_conjecture,
% 1.70/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2054,plain,
% 1.70/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_21,negated_conjecture,
% 1.70/0.99      ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
% 1.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1455,negated_conjecture,
% 1.70/0.99      ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2056,plain,
% 1.70/0.99      ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_15,plain,
% 1.70/0.99      ( m1_orders_2(X0,X1,X2)
% 1.70/0.99      | m1_orders_2(X2,X1,X0)
% 1.70/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.70/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.70/0.99      | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | ~ l1_orders_2(X1)
% 1.70/0.99      | X0 = X2 ),
% 1.70/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_22,negated_conjecture,
% 1.70/0.99      ( l1_orders_2(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_918,plain,
% 1.70/0.99      ( m1_orders_2(X0,X1,X2)
% 1.70/0.99      | m1_orders_2(X2,X1,X0)
% 1.70/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.70/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.70/0.99      | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | X2 = X0
% 1.70/0.99      | sK1 != X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_919,plain,
% 1.70/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(sK1)
% 1.70/0.99      | ~ v3_orders_2(sK1)
% 1.70/0.99      | ~ v4_orders_2(sK1)
% 1.70/0.99      | ~ v5_orders_2(sK1)
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_918]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_26,negated_conjecture,
% 1.70/0.99      ( ~ v2_struct_0(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_25,negated_conjecture,
% 1.70/0.99      ( v3_orders_2(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_24,negated_conjecture,
% 1.70/0.99      ( v4_orders_2(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_23,negated_conjecture,
% 1.70/0.99      ( v5_orders_2(sK1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_921,plain,
% 1.70/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_919,c_26,c_25,c_24,c_23]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_922,plain,
% 1.70/0.99      ( m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_921]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1448,plain,
% 1.70/0.99      ( m1_orders_2(X0_57,sK1,X1_57)
% 1.70/0.99      | m1_orders_2(X1_57,sK1,X0_57)
% 1.70/0.99      | ~ m2_orders_2(X0_57,sK1,X0_59)
% 1.70/0.99      | ~ m2_orders_2(X1_57,sK1,X0_59)
% 1.70/0.99      | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0_57 = X1_57 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_922]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2065,plain,
% 1.70/0.99      ( X0_57 = X1_57
% 1.70/0.99      | m1_orders_2(X0_57,sK1,X1_57) = iProver_top
% 1.70/0.99      | m1_orders_2(X1_57,sK1,X0_57) = iProver_top
% 1.70/0.99      | m2_orders_2(X1_57,sK1,X0_59) != iProver_top
% 1.70/0.99      | m2_orders_2(X0_57,sK1,X0_59) != iProver_top
% 1.70/0.99      | m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2935,plain,
% 1.70/0.99      ( X0_57 = X1_57
% 1.70/0.99      | m1_orders_2(X1_57,sK1,X0_57) = iProver_top
% 1.70/0.99      | m1_orders_2(X0_57,sK1,X1_57) = iProver_top
% 1.70/0.99      | m2_orders_2(X1_57,sK1,sK2) != iProver_top
% 1.70/0.99      | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2056,c_2065]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2986,plain,
% 1.70/0.99      ( sK4 = X0_57
% 1.70/0.99      | m1_orders_2(X0_57,sK1,sK4) = iProver_top
% 1.70/0.99      | m1_orders_2(sK4,sK1,X0_57) = iProver_top
% 1.70/0.99      | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2054,c_2935]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_3016,plain,
% 1.70/0.99      ( sK4 = sK3
% 1.70/0.99      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.70/0.99      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2055,c_2986]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_17,negated_conjecture,
% 1.70/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.70/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_11,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | ~ l1_orders_2(X1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_992,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | sK1 != X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_993,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,sK1,X1)
% 1.70/0.99      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/0.99      | v2_struct_0(sK1)
% 1.70/0.99      | ~ v3_orders_2(sK1)
% 1.70/0.99      | ~ v4_orders_2(sK1)
% 1.70/0.99      | ~ v5_orders_2(sK1) ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_992]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_995,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,sK1,X1)
% 1.70/0.99      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_993,c_26,c_25,c_24,c_23]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1445,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0_57,sK1,X0_59)
% 1.70/0.99      | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_995]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2255,plain,
% 1.70/0.99      ( ~ m2_orders_2(sK3,sK1,sK2)
% 1.70/0.99      | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1445]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1468,plain,( X0_57 = X0_57 ),theory(equality) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2405,plain,
% 1.70/0.99      ( sK4 = sK4 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_1468]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_18,negated_conjecture,
% 1.70/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.70/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1458,negated_conjecture,
% 1.70/0.99      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2053,plain,
% 1.70/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.70/0.99      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_16,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.70/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.70/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.70/0.99      | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | ~ l1_orders_2(X1)
% 1.70/0.99      | X0 = X2 ),
% 1.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_892,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.70/0.99      | ~ m2_orders_2(X2,X1,X3)
% 1.70/0.99      | ~ m2_orders_2(X0,X1,X3)
% 1.70/0.99      | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | X2 = X0
% 1.70/0.99      | sK1 != X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_893,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v2_struct_0(sK1)
% 1.70/0.99      | ~ v3_orders_2(sK1)
% 1.70/0.99      | ~ v4_orders_2(sK1)
% 1.70/0.99      | ~ v5_orders_2(sK1)
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_892]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_895,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(global_propositional_subsumption,
% 1.70/0.99                [status(thm)],
% 1.70/0.99                [c_893,c_26,c_25,c_24,c_23]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_896,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.70/0.99      | ~ m2_orders_2(X0,sK1,X2)
% 1.70/0.99      | ~ m2_orders_2(X1,sK1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0 = X1 ),
% 1.70/0.99      inference(renaming,[status(thm)],[c_895]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1449,plain,
% 1.70/0.99      ( ~ m1_orders_2(X0_57,sK1,X1_57)
% 1.70/0.99      | ~ m1_orders_2(X1_57,sK1,X0_57)
% 1.70/0.99      | ~ m2_orders_2(X0_57,sK1,X0_59)
% 1.70/0.99      | ~ m2_orders_2(X1_57,sK1,X0_59)
% 1.70/0.99      | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | X0_57 = X1_57 ),
% 1.70/0.99      inference(subtyping,[status(esa)],[c_896]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2064,plain,
% 1.70/0.99      ( X0_57 = X1_57
% 1.70/0.99      | m1_orders_2(X0_57,sK1,X1_57) != iProver_top
% 1.70/0.99      | m1_orders_2(X1_57,sK1,X0_57) != iProver_top
% 1.70/0.99      | m2_orders_2(X1_57,sK1,X0_59) != iProver_top
% 1.70/0.99      | m2_orders_2(X0_57,sK1,X0_59) != iProver_top
% 1.70/0.99      | m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2687,plain,
% 1.70/0.99      ( X0_57 = X1_57
% 1.70/0.99      | m1_orders_2(X1_57,sK1,X0_57) != iProver_top
% 1.70/0.99      | m1_orders_2(X0_57,sK1,X1_57) != iProver_top
% 1.70/0.99      | m2_orders_2(X1_57,sK1,sK2) != iProver_top
% 1.70/0.99      | m2_orders_2(X0_57,sK1,sK2) != iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2056,c_2064]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_2740,plain,
% 1.70/0.99      ( sK4 = sK3
% 1.70/0.99      | m1_orders_2(sK4,sK1,sK3) != iProver_top
% 1.70/0.99      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.70/0.99      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.70/0.99      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 1.70/0.99      inference(superposition,[status(thm)],[c_2053,c_2687]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_32,plain,
% 1.70/0.99      ( m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_34,plain,
% 1.70/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_35,plain,
% 1.70/0.99      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.70/0.99      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 1.70/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_12,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | v6_orders_2(X0,X1)
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | ~ l1_orders_2(X1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_10,plain,
% 1.70/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.70/0.99      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | ~ v6_orders_2(k1_xboole_0,X0)
% 1.70/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.70/0.99      | v2_struct_0(X0)
% 1.70/0.99      | ~ v3_orders_2(X0)
% 1.70/0.99      | ~ v4_orders_2(X0)
% 1.70/0.99      | ~ v5_orders_2(X0)
% 1.70/0.99      | ~ l1_orders_2(X0) ),
% 1.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_658,plain,
% 1.70/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.70/0.99      | ~ m2_orders_2(k1_xboole_0,X3,X4)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | ~ m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X3)),k9_setfam_1(u1_struct_0(X3)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
% 1.70/0.99      | v2_struct_0(X1)
% 1.70/0.99      | v2_struct_0(X3)
% 1.70/0.99      | ~ v3_orders_2(X1)
% 1.70/0.99      | ~ v3_orders_2(X3)
% 1.70/0.99      | ~ v4_orders_2(X1)
% 1.70/0.99      | ~ v4_orders_2(X3)
% 1.70/0.99      | ~ v5_orders_2(X1)
% 1.70/0.99      | ~ v5_orders_2(X3)
% 1.70/0.99      | ~ l1_orders_2(X1)
% 1.70/0.99      | ~ l1_orders_2(X3)
% 1.70/0.99      | X3 != X1
% 1.70/0.99      | k1_xboole_0 != X0 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_10]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_659,plain,
% 1.70/0.99      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.70/0.99      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.70/0.99      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/0.99      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.70/1.00      | v2_struct_0(X0)
% 1.70/1.00      | ~ v3_orders_2(X0)
% 1.70/1.00      | ~ v4_orders_2(X0)
% 1.70/1.00      | ~ v5_orders_2(X0)
% 1.70/1.00      | ~ l1_orders_2(X0) ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_658]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_683,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.70/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.70/1.00      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | v2_struct_0(X0)
% 1.70/1.00      | ~ v3_orders_2(X0)
% 1.70/1.00      | ~ v4_orders_2(X0)
% 1.70/1.00      | ~ v5_orders_2(X0)
% 1.70/1.00      | ~ l1_orders_2(X0) ),
% 1.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_659,c_11]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_767,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.70/1.00      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.70/1.00      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | v2_struct_0(X0)
% 1.70/1.00      | ~ v3_orders_2(X0)
% 1.70/1.00      | ~ v4_orders_2(X0)
% 1.70/1.00      | ~ v5_orders_2(X0)
% 1.70/1.00      | sK1 != X0 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_683,c_22]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_768,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.70/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.70/1.00      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | v2_struct_0(sK1)
% 1.70/1.00      | ~ v3_orders_2(sK1)
% 1.70/1.00      | ~ v4_orders_2(sK1)
% 1.70/1.00      | ~ v5_orders_2(sK1) ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_767]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_772,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0)
% 1.70/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1)
% 1.70/1.00      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_768,c_26,c_25,c_24,c_23]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1454,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0_59)
% 1.70/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,X1_59)
% 1.70/1.00      | ~ m1_orders_1(X1_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_772]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1466,plain,
% 1.70/1.00      ( sP0_iProver_split ),
% 1.70/1.00      inference(splitting,
% 1.70/1.00                [splitting(split),new_symbols(definition,[])],
% 1.70/1.00                [c_1454]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1465,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,X0_59)
% 1.70/1.00      | ~ m1_orders_1(X0_59,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ sP0_iProver_split ),
% 1.70/1.00      inference(splitting,
% 1.70/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.70/1.00                [c_1454]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1514,plain,
% 1.70/1.00      ( ~ m2_orders_2(k1_xboole_0,sK1,sK2)
% 1.70/1.00      | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | ~ sP0_iProver_split ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1465]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2252,plain,
% 1.70/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.70/1.00      | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))
% 1.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1445]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2253,plain,
% 1.70/1.00      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.70/1.00      | m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) != iProver_top
% 1.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2252]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1475,plain,
% 1.70/1.00      ( ~ m2_orders_2(X0_57,X0_58,X0_59)
% 1.70/1.00      | m2_orders_2(X1_57,X0_58,X0_59)
% 1.70/1.00      | X1_57 != X0_57 ),
% 1.70/1.00      theory(equality) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2272,plain,
% 1.70/1.00      ( m2_orders_2(X0_57,sK1,sK2)
% 1.70/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.70/1.00      | X0_57 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1475]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2274,plain,
% 1.70/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.70/1.00      | m2_orders_2(k1_xboole_0,sK1,sK2)
% 1.70/1.00      | k1_xboole_0 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2272]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_13,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | r1_tarski(X0,X2)
% 1.70/1.00      | v2_struct_0(X1)
% 1.70/1.00      | ~ v3_orders_2(X1)
% 1.70/1.00      | ~ v4_orders_2(X1)
% 1.70/1.00      | ~ v5_orders_2(X1)
% 1.70/1.00      | ~ l1_orders_2(X1) ),
% 1.70/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_971,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | r1_tarski(X0,X2)
% 1.70/1.00      | v2_struct_0(X1)
% 1.70/1.00      | ~ v3_orders_2(X1)
% 1.70/1.00      | ~ v4_orders_2(X1)
% 1.70/1.00      | ~ v5_orders_2(X1)
% 1.70/1.00      | sK1 != X1 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_972,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(X0,X1)
% 1.70/1.00      | v2_struct_0(sK1)
% 1.70/1.00      | ~ v3_orders_2(sK1)
% 1.70/1.00      | ~ v4_orders_2(sK1)
% 1.70/1.00      | ~ v5_orders_2(sK1) ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_971]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_976,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(X0,X1) ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_972,c_26,c_25,c_24,c_23]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1446,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,sK1,X1_57)
% 1.70/1.00      | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(X0_57,X1_57) ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_976]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2294,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,sK1,sK4)
% 1.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(X0_57,sK4) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2429,plain,
% 1.70/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(sK3,sK4) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2294]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2430,plain,
% 1.70/1.00      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.70/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_0,plain,
% 1.70/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.70/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1464,plain,
% 1.70/1.00      ( ~ r1_tarski(X0_57,X1_57) | r2_xboole_0(X0_57,X1_57) | X1_57 = X0_57 ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2388,plain,
% 1.70/1.00      ( ~ r1_tarski(sK3,X0_57) | r2_xboole_0(sK3,X0_57) | X0_57 = sK3 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1464]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2480,plain,
% 1.70/1.00      ( ~ r1_tarski(sK3,sK4) | r2_xboole_0(sK3,sK4) | sK4 = sK3 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2388]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2481,plain,
% 1.70/1.00      ( sK4 = sK3
% 1.70/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 1.70/1.00      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2480]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1484,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,X0_58,X1_57)
% 1.70/1.00      | m1_orders_2(X2_57,X0_58,X3_57)
% 1.70/1.00      | X2_57 != X0_57
% 1.70/1.00      | X3_57 != X1_57 ),
% 1.70/1.00      theory(equality) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2282,plain,
% 1.70/1.00      ( m1_orders_2(X0_57,sK1,X1_57)
% 1.70/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.70/1.00      | X1_57 != sK4
% 1.70/1.00      | X0_57 != sK3 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1484]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2404,plain,
% 1.70/1.00      ( m1_orders_2(X0_57,sK1,sK4)
% 1.70/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.70/1.00      | X0_57 != sK3
% 1.70/1.00      | sK4 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2282]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2534,plain,
% 1.70/1.00      ( m1_orders_2(sK4,sK1,sK4)
% 1.70/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.70/1.00      | sK4 != sK4
% 1.70/1.00      | sK4 != sK3 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2404]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2535,plain,
% 1.70/1.00      ( sK4 != sK4
% 1.70/1.00      | sK4 != sK3
% 1.70/1.00      | m1_orders_2(sK4,sK1,sK4) = iProver_top
% 1.70/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2534]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_14,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | v2_struct_0(X1)
% 1.70/1.00      | ~ v3_orders_2(X1)
% 1.70/1.00      | ~ v4_orders_2(X1)
% 1.70/1.00      | ~ v5_orders_2(X1)
% 1.70/1.00      | ~ l1_orders_2(X1)
% 1.70/1.00      | k1_xboole_0 = X2 ),
% 1.70/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_944,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.70/1.00      | ~ m1_orders_2(X2,X1,X0)
% 1.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.70/1.00      | v2_struct_0(X1)
% 1.70/1.00      | ~ v3_orders_2(X1)
% 1.70/1.00      | ~ v4_orders_2(X1)
% 1.70/1.00      | ~ v5_orders_2(X1)
% 1.70/1.00      | sK1 != X1
% 1.70/1.00      | k1_xboole_0 = X2 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_945,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 1.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | v2_struct_0(sK1)
% 1.70/1.00      | ~ v3_orders_2(sK1)
% 1.70/1.00      | ~ v4_orders_2(sK1)
% 1.70/1.00      | ~ v5_orders_2(sK1)
% 1.70/1.00      | k1_xboole_0 = X0 ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_944]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_949,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.70/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 1.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | k1_xboole_0 = X0 ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_945,c_26,c_25,c_24,c_23]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1447,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,sK1,X1_57)
% 1.70/1.00      | ~ m1_orders_2(X1_57,sK1,X0_57)
% 1.70/1.00      | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | k1_xboole_0 = X0_57 ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_949]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2334,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,sK1,sK4)
% 1.70/1.00      | ~ m1_orders_2(sK4,sK1,X0_57)
% 1.70/1.00      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | k1_xboole_0 = sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1447]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2701,plain,
% 1.70/1.00      ( ~ m1_orders_2(sK4,sK1,sK4)
% 1.70/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | k1_xboole_0 = sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2334]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2705,plain,
% 1.70/1.00      ( k1_xboole_0 = sK4
% 1.70/1.00      | m1_orders_2(sK4,sK1,sK4) != iProver_top
% 1.70/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2701]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2743,plain,
% 1.70/1.00      ( r2_xboole_0(sK3,sK4) = iProver_top ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_2740,c_21,c_32,c_19,c_34,c_35,c_1466,c_1514,c_2253,c_2274,
% 1.70/1.00                 c_2405,c_2430,c_2481,c_2535,c_2705]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2745,plain,
% 1.70/1.00      ( r2_xboole_0(sK3,sK4) ),
% 1.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2743]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3,plain,
% 1.70/1.00      ( ~ r2_xboole_0(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 1.70/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1461,plain,
% 1.70/1.00      ( ~ r2_xboole_0(X0_57,X1_57) | ~ r2_xboole_0(X1_57,X0_57) ),
% 1.70/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2050,plain,
% 1.70/1.00      ( r2_xboole_0(X0_57,X1_57) != iProver_top
% 1.70/1.00      | r2_xboole_0(X1_57,X0_57) != iProver_top ),
% 1.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2748,plain,
% 1.70/1.00      ( r2_xboole_0(sK4,sK3) != iProver_top ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_2743,c_2050]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2754,plain,
% 1.70/1.00      ( ~ r2_xboole_0(sK4,sK3) ),
% 1.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2748]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2304,plain,
% 1.70/1.00      ( ~ m1_orders_2(X0_57,sK1,sK3)
% 1.70/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(X0_57,sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2909,plain,
% 1.70/1.00      ( ~ m1_orders_2(sK4,sK1,sK3)
% 1.70/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.70/1.00      | r1_tarski(sK4,sK3) ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2304]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3023,plain,
% 1.70/1.00      ( m1_orders_2(sK4,sK1,sK3) | m1_orders_2(sK3,sK1,sK4) | sK4 = sK3 ),
% 1.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3016]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2573,plain,
% 1.70/1.00      ( ~ r1_tarski(X0_57,sK3) | r2_xboole_0(X0_57,sK3) | sK3 = X0_57 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1464]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3045,plain,
% 1.70/1.00      ( ~ r1_tarski(sK4,sK3) | r2_xboole_0(sK4,sK3) | sK3 = sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2573]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_1473,plain,
% 1.70/1.00      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 1.70/1.00      theory(equality) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2561,plain,
% 1.70/1.00      ( X0_57 != X1_57 | sK4 != X1_57 | sK4 = X0_57 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_1473]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2780,plain,
% 1.70/1.00      ( X0_57 != sK4 | sK4 = X0_57 | sK4 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2561]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3084,plain,
% 1.70/1.00      ( sK4 != sK4 | sK4 = sK3 | sK3 != sK4 ),
% 1.70/1.00      inference(instantiation,[status(thm)],[c_2780]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3111,plain,
% 1.70/1.00      ( sK4 = sK3 ),
% 1.70/1.00      inference(global_propositional_subsumption,
% 1.70/1.00                [status(thm)],
% 1.70/1.00                [c_3016,c_21,c_20,c_17,c_2255,c_2405,c_2745,c_2754,c_2909,
% 1.70/1.00                 c_3023,c_3045,c_3084]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3116,plain,
% 1.70/1.00      ( r2_xboole_0(sK3,sK3) != iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3111,c_2748]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3118,plain,
% 1.70/1.00      ( r2_xboole_0(sK3,sK3) = iProver_top ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_3111,c_2743]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3133,plain,
% 1.70/1.00      ( $false ),
% 1.70/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3116,c_3118]) ).
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.70/1.00  
% 1.70/1.00  ------                               Statistics
% 1.70/1.00  
% 1.70/1.00  ------ General
% 1.70/1.00  
% 1.70/1.00  abstr_ref_over_cycles:                  0
% 1.70/1.00  abstr_ref_under_cycles:                 0
% 1.70/1.00  gc_basic_clause_elim:                   0
% 1.70/1.00  forced_gc_time:                         0
% 1.70/1.00  parsing_time:                           0.012
% 1.70/1.00  unif_index_cands_time:                  0.
% 1.70/1.00  unif_index_add_time:                    0.
% 1.70/1.00  orderings_time:                         0.
% 1.70/1.00  out_proof_time:                         0.011
% 1.70/1.00  total_time:                             0.13
% 1.70/1.00  num_of_symbols:                         67
% 1.70/1.00  num_of_terms:                           2030
% 1.70/1.00  
% 1.70/1.00  ------ Preprocessing
% 1.70/1.00  
% 1.70/1.00  num_of_splits:                          2
% 1.70/1.00  num_of_split_atoms:                     1
% 1.70/1.00  num_of_reused_defs:                     1
% 1.70/1.00  num_eq_ax_congr_red:                    40
% 1.70/1.00  num_of_sem_filtered_clauses:            2
% 1.70/1.00  num_of_subtypes:                        9
% 1.70/1.00  monotx_restored_types:                  1
% 1.70/1.00  sat_num_of_epr_types:                   0
% 1.70/1.00  sat_num_of_non_cyclic_types:            0
% 1.70/1.00  sat_guarded_non_collapsed_types:        1
% 1.70/1.00  num_pure_diseq_elim:                    0
% 1.70/1.00  simp_replaced_by:                       0
% 1.70/1.00  res_preprocessed:                       123
% 1.70/1.00  prep_upred:                             0
% 1.70/1.00  prep_unflattend:                        24
% 1.70/1.00  smt_new_axioms:                         0
% 1.70/1.00  pred_elim_cands:                        7
% 1.70/1.00  pred_elim:                              7
% 1.70/1.00  pred_elim_cl:                           7
% 1.70/1.00  pred_elim_cycles:                       14
% 1.70/1.00  merged_defs:                            8
% 1.70/1.00  merged_defs_ncl:                        0
% 1.70/1.00  bin_hyper_res:                          8
% 1.70/1.00  prep_cycles:                            4
% 1.70/1.00  pred_elim_time:                         0.025
% 1.70/1.00  splitting_time:                         0.
% 1.70/1.00  sem_filter_time:                        0.
% 1.70/1.00  monotx_time:                            0.001
% 1.70/1.00  subtype_inf_time:                       0.001
% 1.70/1.00  
% 1.70/1.00  ------ Problem properties
% 1.70/1.00  
% 1.70/1.00  clauses:                                22
% 1.70/1.00  conjectures:                            5
% 1.70/1.00  epr:                                    10
% 1.70/1.00  horn:                                   16
% 1.70/1.00  ground:                                 6
% 1.70/1.00  unary:                                  5
% 1.70/1.00  binary:                                 4
% 1.70/1.00  lits:                                   71
% 1.70/1.00  lits_eq:                                9
% 1.70/1.00  fd_pure:                                0
% 1.70/1.00  fd_pseudo:                              0
% 1.70/1.00  fd_cond:                                4
% 1.70/1.00  fd_pseudo_cond:                         3
% 1.70/1.00  ac_symbols:                             0
% 1.70/1.00  
% 1.70/1.00  ------ Propositional Solver
% 1.70/1.00  
% 1.70/1.00  prop_solver_calls:                      27
% 1.70/1.00  prop_fast_solver_calls:                 1282
% 1.70/1.00  smt_solver_calls:                       0
% 1.70/1.00  smt_fast_solver_calls:                  0
% 1.70/1.00  prop_num_of_clauses:                    561
% 1.70/1.00  prop_preprocess_simplified:             3723
% 1.70/1.00  prop_fo_subsumed:                       58
% 1.70/1.00  prop_solver_time:                       0.
% 1.70/1.00  smt_solver_time:                        0.
% 1.70/1.00  smt_fast_solver_time:                   0.
% 1.70/1.00  prop_fast_solver_time:                  0.
% 1.70/1.00  prop_unsat_core_time:                   0.
% 1.70/1.00  
% 1.70/1.00  ------ QBF
% 1.70/1.00  
% 1.70/1.00  qbf_q_res:                              0
% 1.70/1.00  qbf_num_tautologies:                    0
% 1.70/1.00  qbf_prep_cycles:                        0
% 1.70/1.00  
% 1.70/1.00  ------ BMC1
% 1.70/1.00  
% 1.70/1.00  bmc1_current_bound:                     -1
% 1.70/1.00  bmc1_last_solved_bound:                 -1
% 1.70/1.00  bmc1_unsat_core_size:                   -1
% 1.70/1.00  bmc1_unsat_core_parents_size:           -1
% 1.70/1.00  bmc1_merge_next_fun:                    0
% 1.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.70/1.00  
% 1.70/1.00  ------ Instantiation
% 1.70/1.00  
% 1.70/1.00  inst_num_of_clauses:                    140
% 1.70/1.00  inst_num_in_passive:                    4
% 1.70/1.00  inst_num_in_active:                     128
% 1.70/1.00  inst_num_in_unprocessed:                8
% 1.70/1.00  inst_num_of_loops:                      150
% 1.70/1.00  inst_num_of_learning_restarts:          0
% 1.70/1.00  inst_num_moves_active_passive:          16
% 1.70/1.00  inst_lit_activity:                      0
% 1.70/1.00  inst_lit_activity_moves:                0
% 1.70/1.00  inst_num_tautologies:                   0
% 1.70/1.00  inst_num_prop_implied:                  0
% 1.70/1.00  inst_num_existing_simplified:           0
% 1.70/1.00  inst_num_eq_res_simplified:             0
% 1.70/1.00  inst_num_child_elim:                    0
% 1.70/1.00  inst_num_of_dismatching_blockings:      10
% 1.70/1.00  inst_num_of_non_proper_insts:           177
% 1.70/1.00  inst_num_of_duplicates:                 0
% 1.70/1.00  inst_inst_num_from_inst_to_res:         0
% 1.70/1.00  inst_dismatching_checking_time:         0.
% 1.70/1.00  
% 1.70/1.00  ------ Resolution
% 1.70/1.00  
% 1.70/1.00  res_num_of_clauses:                     0
% 1.70/1.00  res_num_in_passive:                     0
% 1.70/1.00  res_num_in_active:                      0
% 1.70/1.00  res_num_of_loops:                       127
% 1.70/1.00  res_forward_subset_subsumed:            35
% 1.70/1.00  res_backward_subset_subsumed:           0
% 1.70/1.00  res_forward_subsumed:                   0
% 1.70/1.00  res_backward_subsumed:                  0
% 1.70/1.00  res_forward_subsumption_resolution:     3
% 1.70/1.00  res_backward_subsumption_resolution:    0
% 1.70/1.00  res_clause_to_clause_subsumption:       120
% 1.70/1.00  res_orphan_elimination:                 0
% 1.70/1.00  res_tautology_del:                      46
% 1.70/1.00  res_num_eq_res_simplified:              0
% 1.70/1.00  res_num_sel_changes:                    0
% 1.70/1.00  res_moves_from_active_to_pass:          0
% 1.70/1.00  
% 1.70/1.00  ------ Superposition
% 1.70/1.00  
% 1.70/1.00  sup_time_total:                         0.
% 1.70/1.00  sup_time_generating:                    0.
% 1.70/1.00  sup_time_sim_full:                      0.
% 1.70/1.00  sup_time_sim_immed:                     0.
% 1.70/1.00  
% 1.70/1.00  sup_num_of_clauses:                     27
% 1.70/1.00  sup_num_in_active:                      20
% 1.70/1.00  sup_num_in_passive:                     7
% 1.70/1.00  sup_num_of_loops:                       28
% 1.70/1.00  sup_fw_superposition:                   11
% 1.70/1.00  sup_bw_superposition:                   6
% 1.70/1.00  sup_immediate_simplified:               2
% 1.70/1.00  sup_given_eliminated:                   0
% 1.70/1.00  comparisons_done:                       0
% 1.70/1.00  comparisons_avoided:                    0
% 1.70/1.00  
% 1.70/1.00  ------ Simplifications
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  sim_fw_subset_subsumed:                 3
% 1.70/1.00  sim_bw_subset_subsumed:                 0
% 1.70/1.00  sim_fw_subsumed:                        1
% 1.70/1.00  sim_bw_subsumed:                        1
% 1.70/1.00  sim_fw_subsumption_res:                 2
% 1.70/1.00  sim_bw_subsumption_res:                 0
% 1.70/1.00  sim_tautology_del:                      1
% 1.70/1.00  sim_eq_tautology_del:                   1
% 1.70/1.00  sim_eq_res_simp:                        0
% 1.70/1.00  sim_fw_demodulated:                     0
% 1.70/1.00  sim_bw_demodulated:                     8
% 1.70/1.00  sim_light_normalised:                   0
% 1.70/1.00  sim_joinable_taut:                      0
% 1.70/1.00  sim_joinable_simp:                      0
% 1.70/1.00  sim_ac_normalised:                      0
% 1.70/1.00  sim_smt_subsumption:                    0
% 1.70/1.00  
%------------------------------------------------------------------------------
