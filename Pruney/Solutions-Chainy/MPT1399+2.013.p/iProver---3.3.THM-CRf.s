%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:34 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 364 expanded)
%              Number of clauses        :   60 (  71 expanded)
%              Number of leaves         :   19 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  442 (3484 expanded)
%              Number of equality atoms :   80 ( 347 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f68,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f73,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f46,f70])).

cnf(c_2,negated_conjecture,
    ( k3_subset_1(X0,sK2) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,negated_conjecture,
    ( r1_tarski(sK2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_272,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_262,c_15])).

cnf(c_14,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_346,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_347,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_438,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_347])).

cnf(c_439,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_482,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X2)
    | k3_subset_1(u1_struct_0(sK0),X0) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_439])).

cnf(c_483,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),X0))
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_962,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1335,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_962])).

cnf(c_1336,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1335,c_2])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_61,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_63,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_64,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_66,plain,
    ( l1_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_0,negated_conjecture,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_314,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_315,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_21])).

cnf(c_320,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_319])).

cnf(c_385,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_320])).

cnf(c_386,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_392,plain,
    ( v4_pre_topc(sK2,sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_4])).

cnf(c_394,plain,
    ( v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_303,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_304,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_59,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_306,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_22,c_21,c_59])).

cnf(c_965,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_289,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_341,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_289,c_21])).

cnf(c_342,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_978,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_965,c_342])).

cnf(c_1218,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_1339,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_24,c_26,c_27,c_63,c_66,c_394,c_978,c_1219])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_970,plain,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_970,c_2])).

cnf(c_1344,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1339,c_987])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.69/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.69/1.06  
% 0.69/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.69/1.06  
% 0.69/1.06  ------  iProver source info
% 0.69/1.06  
% 0.69/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.69/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.69/1.06  git: non_committed_changes: false
% 0.69/1.06  git: last_make_outside_of_git: false
% 0.69/1.06  
% 0.69/1.06  ------ 
% 0.69/1.06  
% 0.69/1.06  ------ Input Options
% 0.69/1.06  
% 0.69/1.06  --out_options                           all
% 0.69/1.06  --tptp_safe_out                         true
% 0.69/1.06  --problem_path                          ""
% 0.69/1.06  --include_path                          ""
% 0.69/1.06  --clausifier                            res/vclausify_rel
% 0.69/1.06  --clausifier_options                    --mode clausify
% 0.69/1.06  --stdin                                 false
% 0.69/1.06  --stats_out                             all
% 0.69/1.06  
% 0.69/1.06  ------ General Options
% 0.69/1.06  
% 0.69/1.06  --fof                                   false
% 0.69/1.06  --time_out_real                         305.
% 0.69/1.06  --time_out_virtual                      -1.
% 0.69/1.06  --symbol_type_check                     false
% 0.69/1.06  --clausify_out                          false
% 0.69/1.06  --sig_cnt_out                           false
% 0.69/1.06  --trig_cnt_out                          false
% 0.69/1.06  --trig_cnt_out_tolerance                1.
% 0.69/1.06  --trig_cnt_out_sk_spl                   false
% 0.69/1.06  --abstr_cl_out                          false
% 0.69/1.06  
% 0.69/1.06  ------ Global Options
% 0.69/1.06  
% 0.69/1.06  --schedule                              default
% 0.69/1.06  --add_important_lit                     false
% 0.69/1.06  --prop_solver_per_cl                    1000
% 0.69/1.06  --min_unsat_core                        false
% 0.69/1.06  --soft_assumptions                      false
% 0.69/1.06  --soft_lemma_size                       3
% 0.69/1.06  --prop_impl_unit_size                   0
% 0.69/1.06  --prop_impl_unit                        []
% 0.69/1.06  --share_sel_clauses                     true
% 0.69/1.06  --reset_solvers                         false
% 0.69/1.06  --bc_imp_inh                            [conj_cone]
% 0.69/1.06  --conj_cone_tolerance                   3.
% 0.69/1.06  --extra_neg_conj                        none
% 0.69/1.06  --large_theory_mode                     true
% 0.69/1.06  --prolific_symb_bound                   200
% 0.69/1.06  --lt_threshold                          2000
% 0.69/1.06  --clause_weak_htbl                      true
% 0.69/1.06  --gc_record_bc_elim                     false
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing Options
% 0.69/1.06  
% 0.69/1.06  --preprocessing_flag                    true
% 0.69/1.06  --time_out_prep_mult                    0.1
% 0.69/1.06  --splitting_mode                        input
% 0.69/1.06  --splitting_grd                         true
% 0.69/1.06  --splitting_cvd                         false
% 0.69/1.06  --splitting_cvd_svl                     false
% 0.69/1.06  --splitting_nvd                         32
% 0.69/1.06  --sub_typing                            true
% 0.69/1.06  --prep_gs_sim                           true
% 0.69/1.06  --prep_unflatten                        true
% 0.69/1.06  --prep_res_sim                          true
% 0.69/1.06  --prep_upred                            true
% 0.69/1.06  --prep_sem_filter                       exhaustive
% 0.69/1.06  --prep_sem_filter_out                   false
% 0.69/1.06  --pred_elim                             true
% 0.69/1.06  --res_sim_input                         true
% 0.69/1.06  --eq_ax_congr_red                       true
% 0.69/1.06  --pure_diseq_elim                       true
% 0.69/1.06  --brand_transform                       false
% 0.69/1.06  --non_eq_to_eq                          false
% 0.69/1.06  --prep_def_merge                        true
% 0.69/1.06  --prep_def_merge_prop_impl              false
% 0.69/1.06  --prep_def_merge_mbd                    true
% 0.69/1.06  --prep_def_merge_tr_red                 false
% 0.69/1.06  --prep_def_merge_tr_cl                  false
% 0.69/1.06  --smt_preprocessing                     true
% 0.69/1.06  --smt_ac_axioms                         fast
% 0.69/1.06  --preprocessed_out                      false
% 0.69/1.06  --preprocessed_stats                    false
% 0.69/1.06  
% 0.69/1.06  ------ Abstraction refinement Options
% 0.69/1.06  
% 0.69/1.06  --abstr_ref                             []
% 0.69/1.06  --abstr_ref_prep                        false
% 0.69/1.06  --abstr_ref_until_sat                   false
% 0.69/1.06  --abstr_ref_sig_restrict                funpre
% 0.69/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.69/1.06  --abstr_ref_under                       []
% 0.69/1.06  
% 0.69/1.06  ------ SAT Options
% 0.69/1.06  
% 0.69/1.06  --sat_mode                              false
% 0.69/1.06  --sat_fm_restart_options                ""
% 0.69/1.06  --sat_gr_def                            false
% 0.69/1.06  --sat_epr_types                         true
% 0.69/1.06  --sat_non_cyclic_types                  false
% 0.69/1.06  --sat_finite_models                     false
% 0.69/1.06  --sat_fm_lemmas                         false
% 0.69/1.06  --sat_fm_prep                           false
% 0.69/1.06  --sat_fm_uc_incr                        true
% 0.69/1.06  --sat_out_model                         small
% 0.69/1.06  --sat_out_clauses                       false
% 0.69/1.06  
% 0.69/1.06  ------ QBF Options
% 0.69/1.06  
% 0.69/1.06  --qbf_mode                              false
% 0.69/1.06  --qbf_elim_univ                         false
% 0.69/1.06  --qbf_dom_inst                          none
% 0.69/1.06  --qbf_dom_pre_inst                      false
% 0.69/1.06  --qbf_sk_in                             false
% 0.69/1.06  --qbf_pred_elim                         true
% 0.69/1.06  --qbf_split                             512
% 0.69/1.06  
% 0.69/1.06  ------ BMC1 Options
% 0.69/1.06  
% 0.69/1.06  --bmc1_incremental                      false
% 0.69/1.06  --bmc1_axioms                           reachable_all
% 0.69/1.06  --bmc1_min_bound                        0
% 0.69/1.06  --bmc1_max_bound                        -1
% 0.69/1.06  --bmc1_max_bound_default                -1
% 0.69/1.06  --bmc1_symbol_reachability              true
% 0.69/1.06  --bmc1_property_lemmas                  false
% 0.69/1.06  --bmc1_k_induction                      false
% 0.69/1.06  --bmc1_non_equiv_states                 false
% 0.69/1.06  --bmc1_deadlock                         false
% 0.69/1.06  --bmc1_ucm                              false
% 0.69/1.06  --bmc1_add_unsat_core                   none
% 0.69/1.06  --bmc1_unsat_core_children              false
% 0.69/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.69/1.06  --bmc1_out_stat                         full
% 0.69/1.06  --bmc1_ground_init                      false
% 0.69/1.06  --bmc1_pre_inst_next_state              false
% 0.69/1.06  --bmc1_pre_inst_state                   false
% 0.69/1.06  --bmc1_pre_inst_reach_state             false
% 0.69/1.06  --bmc1_out_unsat_core                   false
% 0.69/1.06  --bmc1_aig_witness_out                  false
% 0.69/1.06  --bmc1_verbose                          false
% 0.69/1.06  --bmc1_dump_clauses_tptp                false
% 0.69/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.69/1.06  --bmc1_dump_file                        -
% 0.69/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.69/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.69/1.06  --bmc1_ucm_extend_mode                  1
% 0.69/1.06  --bmc1_ucm_init_mode                    2
% 0.69/1.06  --bmc1_ucm_cone_mode                    none
% 0.69/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.69/1.06  --bmc1_ucm_relax_model                  4
% 0.69/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.69/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.69/1.06  --bmc1_ucm_layered_model                none
% 0.69/1.06  --bmc1_ucm_max_lemma_size               10
% 0.69/1.06  
% 0.69/1.06  ------ AIG Options
% 0.69/1.06  
% 0.69/1.06  --aig_mode                              false
% 0.69/1.06  
% 0.69/1.06  ------ Instantiation Options
% 0.69/1.06  
% 0.69/1.06  --instantiation_flag                    true
% 0.69/1.06  --inst_sos_flag                         false
% 0.69/1.06  --inst_sos_phase                        true
% 0.69/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.69/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.69/1.06  --inst_lit_sel_side                     num_symb
% 0.69/1.06  --inst_solver_per_active                1400
% 0.69/1.06  --inst_solver_calls_frac                1.
% 0.69/1.06  --inst_passive_queue_type               priority_queues
% 0.69/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.69/1.06  --inst_passive_queues_freq              [25;2]
% 0.69/1.06  --inst_dismatching                      true
% 0.69/1.06  --inst_eager_unprocessed_to_passive     true
% 0.69/1.06  --inst_prop_sim_given                   true
% 0.69/1.06  --inst_prop_sim_new                     false
% 0.69/1.06  --inst_subs_new                         false
% 0.69/1.06  --inst_eq_res_simp                      false
% 0.69/1.06  --inst_subs_given                       false
% 0.69/1.06  --inst_orphan_elimination               true
% 0.69/1.06  --inst_learning_loop_flag               true
% 0.69/1.06  --inst_learning_start                   3000
% 0.69/1.06  --inst_learning_factor                  2
% 0.69/1.06  --inst_start_prop_sim_after_learn       3
% 0.69/1.06  --inst_sel_renew                        solver
% 0.69/1.06  --inst_lit_activity_flag                true
% 0.69/1.06  --inst_restr_to_given                   false
% 0.69/1.06  --inst_activity_threshold               500
% 0.69/1.06  --inst_out_proof                        true
% 0.69/1.06  
% 0.69/1.06  ------ Resolution Options
% 0.69/1.06  
% 0.69/1.06  --resolution_flag                       true
% 0.69/1.06  --res_lit_sel                           adaptive
% 0.69/1.06  --res_lit_sel_side                      none
% 0.69/1.06  --res_ordering                          kbo
% 0.69/1.06  --res_to_prop_solver                    active
% 0.69/1.06  --res_prop_simpl_new                    false
% 0.69/1.06  --res_prop_simpl_given                  true
% 0.69/1.06  --res_passive_queue_type                priority_queues
% 0.69/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.69/1.06  --res_passive_queues_freq               [15;5]
% 0.69/1.06  --res_forward_subs                      full
% 0.69/1.06  --res_backward_subs                     full
% 0.69/1.06  --res_forward_subs_resolution           true
% 0.69/1.06  --res_backward_subs_resolution          true
% 0.69/1.06  --res_orphan_elimination                true
% 0.69/1.06  --res_time_limit                        2.
% 0.69/1.06  --res_out_proof                         true
% 0.69/1.06  
% 0.69/1.06  ------ Superposition Options
% 0.69/1.06  
% 0.69/1.06  --superposition_flag                    true
% 0.69/1.06  --sup_passive_queue_type                priority_queues
% 0.69/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.69/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.69/1.06  --demod_completeness_check              fast
% 0.69/1.06  --demod_use_ground                      true
% 0.69/1.06  --sup_to_prop_solver                    passive
% 0.69/1.06  --sup_prop_simpl_new                    true
% 0.69/1.06  --sup_prop_simpl_given                  true
% 0.69/1.06  --sup_fun_splitting                     false
% 0.69/1.06  --sup_smt_interval                      50000
% 0.69/1.06  
% 0.69/1.06  ------ Superposition Simplification Setup
% 0.69/1.06  
% 0.69/1.06  --sup_indices_passive                   []
% 0.69/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.69/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_full_bw                           [BwDemod]
% 0.69/1.06  --sup_immed_triv                        [TrivRules]
% 0.69/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.69/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_immed_bw_main                     []
% 0.69/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.69/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.06  
% 0.69/1.06  ------ Combination Options
% 0.69/1.06  
% 0.69/1.06  --comb_res_mult                         3
% 0.69/1.06  --comb_sup_mult                         2
% 0.69/1.06  --comb_inst_mult                        10
% 0.69/1.06  
% 0.69/1.06  ------ Debug Options
% 0.69/1.06  
% 0.69/1.06  --dbg_backtrace                         false
% 0.69/1.06  --dbg_dump_prop_clauses                 false
% 0.69/1.06  --dbg_dump_prop_clauses_file            -
% 0.69/1.06  --dbg_out_stat                          false
% 0.69/1.06  ------ Parsing...
% 0.69/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.69/1.06  ------ Proving...
% 0.69/1.06  ------ Problem Properties 
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  clauses                                 12
% 0.69/1.06  conjectures                             6
% 0.69/1.06  EPR                                     1
% 0.69/1.06  Horn                                    11
% 0.69/1.06  unary                                   9
% 0.69/1.06  binary                                  0
% 0.69/1.06  lits                                    22
% 0.69/1.06  lits eq                                 2
% 0.69/1.06  fd_pure                                 0
% 0.69/1.06  fd_pseudo                               0
% 0.69/1.06  fd_cond                                 0
% 0.69/1.06  fd_pseudo_cond                          0
% 0.69/1.06  AC symbols                              0
% 0.69/1.06  
% 0.69/1.06  ------ Schedule dynamic 5 is on 
% 0.69/1.06  
% 0.69/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  ------ 
% 0.69/1.06  Current options:
% 0.69/1.06  ------ 
% 0.69/1.06  
% 0.69/1.06  ------ Input Options
% 0.69/1.06  
% 0.69/1.06  --out_options                           all
% 0.69/1.06  --tptp_safe_out                         true
% 0.69/1.06  --problem_path                          ""
% 0.69/1.06  --include_path                          ""
% 0.69/1.06  --clausifier                            res/vclausify_rel
% 0.69/1.06  --clausifier_options                    --mode clausify
% 0.69/1.06  --stdin                                 false
% 0.69/1.06  --stats_out                             all
% 0.69/1.06  
% 0.69/1.06  ------ General Options
% 0.69/1.06  
% 0.69/1.06  --fof                                   false
% 0.69/1.06  --time_out_real                         305.
% 0.69/1.06  --time_out_virtual                      -1.
% 0.69/1.06  --symbol_type_check                     false
% 0.69/1.06  --clausify_out                          false
% 0.69/1.06  --sig_cnt_out                           false
% 0.69/1.06  --trig_cnt_out                          false
% 0.69/1.06  --trig_cnt_out_tolerance                1.
% 0.69/1.06  --trig_cnt_out_sk_spl                   false
% 0.69/1.06  --abstr_cl_out                          false
% 0.69/1.06  
% 0.69/1.06  ------ Global Options
% 0.69/1.06  
% 0.69/1.06  --schedule                              default
% 0.69/1.06  --add_important_lit                     false
% 0.69/1.06  --prop_solver_per_cl                    1000
% 0.69/1.06  --min_unsat_core                        false
% 0.69/1.06  --soft_assumptions                      false
% 0.69/1.06  --soft_lemma_size                       3
% 0.69/1.06  --prop_impl_unit_size                   0
% 0.69/1.06  --prop_impl_unit                        []
% 0.69/1.06  --share_sel_clauses                     true
% 0.69/1.06  --reset_solvers                         false
% 0.69/1.06  --bc_imp_inh                            [conj_cone]
% 0.69/1.06  --conj_cone_tolerance                   3.
% 0.69/1.06  --extra_neg_conj                        none
% 0.69/1.06  --large_theory_mode                     true
% 0.69/1.06  --prolific_symb_bound                   200
% 0.69/1.06  --lt_threshold                          2000
% 0.69/1.06  --clause_weak_htbl                      true
% 0.69/1.06  --gc_record_bc_elim                     false
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing Options
% 0.69/1.06  
% 0.69/1.06  --preprocessing_flag                    true
% 0.69/1.06  --time_out_prep_mult                    0.1
% 0.69/1.06  --splitting_mode                        input
% 0.69/1.06  --splitting_grd                         true
% 0.69/1.06  --splitting_cvd                         false
% 0.69/1.06  --splitting_cvd_svl                     false
% 0.69/1.06  --splitting_nvd                         32
% 0.69/1.06  --sub_typing                            true
% 0.69/1.06  --prep_gs_sim                           true
% 0.69/1.06  --prep_unflatten                        true
% 0.69/1.06  --prep_res_sim                          true
% 0.69/1.06  --prep_upred                            true
% 0.69/1.06  --prep_sem_filter                       exhaustive
% 0.69/1.06  --prep_sem_filter_out                   false
% 0.69/1.06  --pred_elim                             true
% 0.69/1.06  --res_sim_input                         true
% 0.69/1.06  --eq_ax_congr_red                       true
% 0.69/1.06  --pure_diseq_elim                       true
% 0.69/1.06  --brand_transform                       false
% 0.69/1.06  --non_eq_to_eq                          false
% 0.69/1.06  --prep_def_merge                        true
% 0.69/1.06  --prep_def_merge_prop_impl              false
% 0.69/1.06  --prep_def_merge_mbd                    true
% 0.69/1.06  --prep_def_merge_tr_red                 false
% 0.69/1.06  --prep_def_merge_tr_cl                  false
% 0.69/1.06  --smt_preprocessing                     true
% 0.69/1.06  --smt_ac_axioms                         fast
% 0.69/1.06  --preprocessed_out                      false
% 0.69/1.06  --preprocessed_stats                    false
% 0.69/1.06  
% 0.69/1.06  ------ Abstraction refinement Options
% 0.69/1.06  
% 0.69/1.06  --abstr_ref                             []
% 0.69/1.06  --abstr_ref_prep                        false
% 0.69/1.06  --abstr_ref_until_sat                   false
% 0.69/1.06  --abstr_ref_sig_restrict                funpre
% 0.69/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.69/1.06  --abstr_ref_under                       []
% 0.69/1.06  
% 0.69/1.06  ------ SAT Options
% 0.69/1.06  
% 0.69/1.06  --sat_mode                              false
% 0.69/1.06  --sat_fm_restart_options                ""
% 0.69/1.06  --sat_gr_def                            false
% 0.69/1.06  --sat_epr_types                         true
% 0.69/1.06  --sat_non_cyclic_types                  false
% 0.69/1.06  --sat_finite_models                     false
% 0.69/1.06  --sat_fm_lemmas                         false
% 0.69/1.06  --sat_fm_prep                           false
% 0.69/1.06  --sat_fm_uc_incr                        true
% 0.69/1.06  --sat_out_model                         small
% 0.69/1.06  --sat_out_clauses                       false
% 0.69/1.06  
% 0.69/1.06  ------ QBF Options
% 0.69/1.06  
% 0.69/1.06  --qbf_mode                              false
% 0.69/1.06  --qbf_elim_univ                         false
% 0.69/1.06  --qbf_dom_inst                          none
% 0.69/1.06  --qbf_dom_pre_inst                      false
% 0.69/1.06  --qbf_sk_in                             false
% 0.69/1.06  --qbf_pred_elim                         true
% 0.69/1.06  --qbf_split                             512
% 0.69/1.06  
% 0.69/1.06  ------ BMC1 Options
% 0.69/1.06  
% 0.69/1.06  --bmc1_incremental                      false
% 0.69/1.06  --bmc1_axioms                           reachable_all
% 0.69/1.06  --bmc1_min_bound                        0
% 0.69/1.06  --bmc1_max_bound                        -1
% 0.69/1.06  --bmc1_max_bound_default                -1
% 0.69/1.06  --bmc1_symbol_reachability              true
% 0.69/1.06  --bmc1_property_lemmas                  false
% 0.69/1.06  --bmc1_k_induction                      false
% 0.69/1.06  --bmc1_non_equiv_states                 false
% 0.69/1.06  --bmc1_deadlock                         false
% 0.69/1.06  --bmc1_ucm                              false
% 0.69/1.06  --bmc1_add_unsat_core                   none
% 0.69/1.06  --bmc1_unsat_core_children              false
% 0.69/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.69/1.06  --bmc1_out_stat                         full
% 0.69/1.06  --bmc1_ground_init                      false
% 0.69/1.06  --bmc1_pre_inst_next_state              false
% 0.69/1.06  --bmc1_pre_inst_state                   false
% 0.69/1.06  --bmc1_pre_inst_reach_state             false
% 0.69/1.06  --bmc1_out_unsat_core                   false
% 0.69/1.06  --bmc1_aig_witness_out                  false
% 0.69/1.06  --bmc1_verbose                          false
% 0.69/1.06  --bmc1_dump_clauses_tptp                false
% 0.69/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.69/1.06  --bmc1_dump_file                        -
% 0.69/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.69/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.69/1.06  --bmc1_ucm_extend_mode                  1
% 0.69/1.06  --bmc1_ucm_init_mode                    2
% 0.69/1.06  --bmc1_ucm_cone_mode                    none
% 0.69/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.69/1.06  --bmc1_ucm_relax_model                  4
% 0.69/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.69/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.69/1.06  --bmc1_ucm_layered_model                none
% 0.69/1.06  --bmc1_ucm_max_lemma_size               10
% 0.69/1.06  
% 0.69/1.06  ------ AIG Options
% 0.69/1.06  
% 0.69/1.06  --aig_mode                              false
% 0.69/1.06  
% 0.69/1.06  ------ Instantiation Options
% 0.69/1.06  
% 0.69/1.06  --instantiation_flag                    true
% 0.69/1.06  --inst_sos_flag                         false
% 0.69/1.06  --inst_sos_phase                        true
% 0.69/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.69/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.69/1.06  --inst_lit_sel_side                     none
% 0.69/1.06  --inst_solver_per_active                1400
% 0.69/1.06  --inst_solver_calls_frac                1.
% 0.69/1.06  --inst_passive_queue_type               priority_queues
% 0.69/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.69/1.06  --inst_passive_queues_freq              [25;2]
% 0.69/1.06  --inst_dismatching                      true
% 0.69/1.06  --inst_eager_unprocessed_to_passive     true
% 0.69/1.06  --inst_prop_sim_given                   true
% 0.69/1.06  --inst_prop_sim_new                     false
% 0.69/1.06  --inst_subs_new                         false
% 0.69/1.06  --inst_eq_res_simp                      false
% 0.69/1.06  --inst_subs_given                       false
% 0.69/1.06  --inst_orphan_elimination               true
% 0.69/1.06  --inst_learning_loop_flag               true
% 0.69/1.06  --inst_learning_start                   3000
% 0.69/1.06  --inst_learning_factor                  2
% 0.69/1.06  --inst_start_prop_sim_after_learn       3
% 0.69/1.06  --inst_sel_renew                        solver
% 0.69/1.06  --inst_lit_activity_flag                true
% 0.69/1.06  --inst_restr_to_given                   false
% 0.69/1.06  --inst_activity_threshold               500
% 0.69/1.06  --inst_out_proof                        true
% 0.69/1.06  
% 0.69/1.06  ------ Resolution Options
% 0.69/1.06  
% 0.69/1.06  --resolution_flag                       false
% 0.69/1.06  --res_lit_sel                           adaptive
% 0.69/1.06  --res_lit_sel_side                      none
% 0.69/1.06  --res_ordering                          kbo
% 0.69/1.06  --res_to_prop_solver                    active
% 0.69/1.06  --res_prop_simpl_new                    false
% 0.69/1.06  --res_prop_simpl_given                  true
% 0.69/1.06  --res_passive_queue_type                priority_queues
% 0.69/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.69/1.06  --res_passive_queues_freq               [15;5]
% 0.69/1.06  --res_forward_subs                      full
% 0.69/1.06  --res_backward_subs                     full
% 0.69/1.06  --res_forward_subs_resolution           true
% 0.69/1.06  --res_backward_subs_resolution          true
% 0.69/1.06  --res_orphan_elimination                true
% 0.69/1.06  --res_time_limit                        2.
% 0.69/1.06  --res_out_proof                         true
% 0.69/1.06  
% 0.69/1.06  ------ Superposition Options
% 0.69/1.06  
% 0.69/1.06  --superposition_flag                    true
% 0.69/1.06  --sup_passive_queue_type                priority_queues
% 0.69/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.69/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.69/1.06  --demod_completeness_check              fast
% 0.69/1.06  --demod_use_ground                      true
% 0.69/1.06  --sup_to_prop_solver                    passive
% 0.69/1.06  --sup_prop_simpl_new                    true
% 0.69/1.06  --sup_prop_simpl_given                  true
% 0.69/1.06  --sup_fun_splitting                     false
% 0.69/1.06  --sup_smt_interval                      50000
% 0.69/1.06  
% 0.69/1.06  ------ Superposition Simplification Setup
% 0.69/1.06  
% 0.69/1.06  --sup_indices_passive                   []
% 0.69/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.69/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_full_bw                           [BwDemod]
% 0.69/1.06  --sup_immed_triv                        [TrivRules]
% 0.69/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.69/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_immed_bw_main                     []
% 0.69/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.69/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.06  
% 0.69/1.06  ------ Combination Options
% 0.69/1.06  
% 0.69/1.06  --comb_res_mult                         3
% 0.69/1.06  --comb_sup_mult                         2
% 0.69/1.06  --comb_inst_mult                        10
% 0.69/1.06  
% 0.69/1.06  ------ Debug Options
% 0.69/1.06  
% 0.69/1.06  --dbg_backtrace                         false
% 0.69/1.06  --dbg_dump_prop_clauses                 false
% 0.69/1.06  --dbg_dump_prop_clauses_file            -
% 0.69/1.06  --dbg_out_stat                          false
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  ------ Proving...
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  % SZS status Theorem for theBenchmark.p
% 0.69/1.06  
% 0.69/1.06   Resolution empty clause
% 0.69/1.06  
% 0.69/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.69/1.06  
% 0.69/1.06  fof(f4,axiom,(
% 0.69/1.06    ! [X0] : k2_subset_1(X0) = X0),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f45,plain,(
% 0.69/1.06    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.69/1.06    inference(cnf_transformation,[],[f4])).
% 0.69/1.06  
% 0.69/1.06  fof(f6,axiom,(
% 0.69/1.06    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f47,plain,(
% 0.69/1.06    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.69/1.06    inference(cnf_transformation,[],[f6])).
% 0.69/1.06  
% 0.69/1.06  fof(f3,axiom,(
% 0.69/1.06    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f44,plain,(
% 0.69/1.06    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f3])).
% 0.69/1.06  
% 0.69/1.06  fof(f17,conjecture,(
% 0.69/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f18,negated_conjecture,(
% 0.69/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.69/1.06    inference(negated_conjecture,[],[f17])).
% 0.69/1.06  
% 0.69/1.06  fof(f33,plain,(
% 0.69/1.06    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.69/1.06    inference(ennf_transformation,[],[f18])).
% 0.69/1.06  
% 0.69/1.06  fof(f34,plain,(
% 0.69/1.06    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.06    inference(flattening,[],[f33])).
% 0.69/1.06  
% 0.69/1.06  fof(f36,plain,(
% 0.69/1.06    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.06    inference(nnf_transformation,[],[f34])).
% 0.69/1.06  
% 0.69/1.06  fof(f37,plain,(
% 0.69/1.06    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.06    inference(flattening,[],[f36])).
% 0.69/1.06  
% 0.69/1.06  fof(f40,plain,(
% 0.69/1.06    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.69/1.06    introduced(choice_axiom,[])).
% 0.69/1.06  
% 0.69/1.06  fof(f39,plain,(
% 0.69/1.06    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 0.69/1.06    introduced(choice_axiom,[])).
% 0.69/1.06  
% 0.69/1.06  fof(f38,plain,(
% 0.69/1.06    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.69/1.06    introduced(choice_axiom,[])).
% 0.69/1.06  
% 0.69/1.06  fof(f41,plain,(
% 0.69/1.06    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.69/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 0.69/1.06  
% 0.69/1.06  fof(f68,plain,(
% 0.69/1.06    k1_xboole_0 = sK2),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f69,plain,(
% 0.69/1.06    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.69/1.06    inference(definition_unfolding,[],[f44,f68])).
% 0.69/1.06  
% 0.69/1.06  fof(f70,plain,(
% 0.69/1.06    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.69/1.06    inference(definition_unfolding,[],[f47,f69])).
% 0.69/1.06  
% 0.69/1.06  fof(f73,plain,(
% 0.69/1.06    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.69/1.06    inference(definition_unfolding,[],[f45,f70])).
% 0.69/1.06  
% 0.69/1.06  fof(f8,axiom,(
% 0.69/1.06    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f19,plain,(
% 0.69/1.06    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.69/1.06    inference(ennf_transformation,[],[f8])).
% 0.69/1.06  
% 0.69/1.06  fof(f20,plain,(
% 0.69/1.06    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.69/1.06    inference(flattening,[],[f19])).
% 0.69/1.06  
% 0.69/1.06  fof(f49,plain,(
% 0.69/1.06    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f20])).
% 0.69/1.06  
% 0.69/1.06  fof(f2,axiom,(
% 0.69/1.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f43,plain,(
% 0.69/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f2])).
% 0.69/1.06  
% 0.69/1.06  fof(f72,plain,(
% 0.69/1.06    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.69/1.06    inference(definition_unfolding,[],[f43,f68])).
% 0.69/1.06  
% 0.69/1.06  fof(f10,axiom,(
% 0.69/1.06    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f23,plain,(
% 0.69/1.06    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.69/1.06    inference(ennf_transformation,[],[f10])).
% 0.69/1.06  
% 0.69/1.06  fof(f51,plain,(
% 0.69/1.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f23])).
% 0.69/1.06  
% 0.69/1.06  fof(f67,plain,(
% 0.69/1.06    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f16,axiom,(
% 0.69/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f32,plain,(
% 0.69/1.06    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.69/1.06    inference(ennf_transformation,[],[f16])).
% 0.69/1.06  
% 0.69/1.06  fof(f35,plain,(
% 0.69/1.06    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.69/1.06    inference(nnf_transformation,[],[f32])).
% 0.69/1.06  
% 0.69/1.06  fof(f57,plain,(
% 0.69/1.06    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f35])).
% 0.69/1.06  
% 0.69/1.06  fof(f61,plain,(
% 0.69/1.06    l1_pre_topc(sK0)),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f59,plain,(
% 0.69/1.06    ~v2_struct_0(sK0)),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f62,plain,(
% 0.69/1.06    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f14,axiom,(
% 0.69/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f28,plain,(
% 0.69/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.69/1.06    inference(ennf_transformation,[],[f14])).
% 0.69/1.06  
% 0.69/1.06  fof(f29,plain,(
% 0.69/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.69/1.06    inference(flattening,[],[f28])).
% 0.69/1.06  
% 0.69/1.06  fof(f55,plain,(
% 0.69/1.06    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f29])).
% 0.69/1.06  
% 0.69/1.06  fof(f13,axiom,(
% 0.69/1.06    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f27,plain,(
% 0.69/1.06    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.69/1.06    inference(ennf_transformation,[],[f13])).
% 0.69/1.06  
% 0.69/1.06  fof(f54,plain,(
% 0.69/1.06    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f27])).
% 0.69/1.06  
% 0.69/1.06  fof(f1,axiom,(
% 0.69/1.06    v1_xboole_0(k1_xboole_0)),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f42,plain,(
% 0.69/1.06    v1_xboole_0(k1_xboole_0)),
% 0.69/1.06    inference(cnf_transformation,[],[f1])).
% 0.69/1.06  
% 0.69/1.06  fof(f71,plain,(
% 0.69/1.06    v1_xboole_0(sK2)),
% 0.69/1.06    inference(definition_unfolding,[],[f42,f68])).
% 0.69/1.06  
% 0.69/1.06  fof(f11,axiom,(
% 0.69/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f24,plain,(
% 0.69/1.06    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.69/1.06    inference(ennf_transformation,[],[f11])).
% 0.69/1.06  
% 0.69/1.06  fof(f25,plain,(
% 0.69/1.06    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.69/1.06    inference(flattening,[],[f24])).
% 0.69/1.06  
% 0.69/1.06  fof(f52,plain,(
% 0.69/1.06    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f25])).
% 0.69/1.06  
% 0.69/1.06  fof(f60,plain,(
% 0.69/1.06    v2_pre_topc(sK0)),
% 0.69/1.06    inference(cnf_transformation,[],[f41])).
% 0.69/1.06  
% 0.69/1.06  fof(f7,axiom,(
% 0.69/1.06    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f48,plain,(
% 0.69/1.06    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.69/1.06    inference(cnf_transformation,[],[f7])).
% 0.69/1.06  
% 0.69/1.06  fof(f75,plain,(
% 0.69/1.06    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.69/1.06    inference(definition_unfolding,[],[f48,f68])).
% 0.69/1.06  
% 0.69/1.06  fof(f15,axiom,(
% 0.69/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f30,plain,(
% 0.69/1.06    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.69/1.06    inference(ennf_transformation,[],[f15])).
% 0.69/1.06  
% 0.69/1.06  fof(f31,plain,(
% 0.69/1.06    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.69/1.06    inference(flattening,[],[f30])).
% 0.69/1.06  
% 0.69/1.06  fof(f56,plain,(
% 0.69/1.06    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f31])).
% 0.69/1.06  
% 0.69/1.06  fof(f12,axiom,(
% 0.69/1.06    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f26,plain,(
% 0.69/1.06    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.69/1.06    inference(ennf_transformation,[],[f12])).
% 0.69/1.06  
% 0.69/1.06  fof(f53,plain,(
% 0.69/1.06    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.69/1.06    inference(cnf_transformation,[],[f26])).
% 0.69/1.06  
% 0.69/1.06  fof(f5,axiom,(
% 0.69/1.06    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.69/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.69/1.06  
% 0.69/1.06  fof(f46,plain,(
% 0.69/1.06    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.69/1.06    inference(cnf_transformation,[],[f5])).
% 0.69/1.06  
% 0.69/1.06  fof(f74,plain,(
% 0.69/1.06    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.69/1.06    inference(definition_unfolding,[],[f46,f70])).
% 0.69/1.06  
% 0.69/1.06  cnf(c_2,negated_conjecture,
% 0.69/1.06      ( k3_subset_1(X0,sK2) = X0 ),
% 0.69/1.06      inference(cnf_transformation,[],[f73]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_5,plain,
% 0.69/1.06      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 0.69/1.06      inference(cnf_transformation,[],[f49]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1,negated_conjecture,
% 0.69/1.06      ( r1_tarski(sK2,X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f72]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_7,plain,
% 0.69/1.06      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f51]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_261,plain,
% 0.69/1.06      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK2 != X1 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_262,plain,
% 0.69/1.06      ( ~ r2_hidden(X0,sK2) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_261]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_15,negated_conjecture,
% 0.69/1.06      ( ~ v3_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | r2_hidden(X0,sK2)
% 0.69/1.06      | ~ r2_hidden(sK1,X0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(cnf_transformation,[],[f67]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_272,plain,
% 0.69/1.06      ( ~ v3_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ r2_hidden(sK1,X0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(backward_subsumption_resolution,[status(thm)],[c_262,c_15]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_14,plain,
% 0.69/1.06      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.69/1.06      | ~ v4_pre_topc(X1,X0)
% 0.69/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.69/1.06      | ~ l1_pre_topc(X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f57]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_21,negated_conjecture,
% 0.69/1.06      ( l1_pre_topc(sK0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f61]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_346,plain,
% 0.69/1.06      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.69/1.06      | ~ v4_pre_topc(X1,X0)
% 0.69/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.69/1.06      | sK0 != X0 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_347,plain,
% 0.69/1.06      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.69/1.06      | ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_346]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_438,plain,
% 0.69/1.06      ( ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(X1,sK0)
% 0.69/1.06      | ~ r2_hidden(sK1,X0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | k3_subset_1(u1_struct_0(sK0),X1) != X0
% 0.69/1.06      | sK0 != sK0 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_272,c_347]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_439,plain,
% 0.69/1.06      ( ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.69/1.06      | ~ r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0))
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_438]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_482,plain,
% 0.69/1.06      ( ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.69/1.06      | ~ m1_subset_1(X1,X2)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | v1_xboole_0(X2)
% 0.69/1.06      | k3_subset_1(u1_struct_0(sK0),X0) != X2
% 0.69/1.06      | sK1 != X1 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_5,c_439]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_483,plain,
% 0.69/1.06      ( ~ v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),X0))
% 0.69/1.06      | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),X0)) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_482]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_962,plain,
% 0.69/1.06      ( v4_pre_topc(X0,sK0) != iProver_top
% 0.69/1.06      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
% 0.69/1.06      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top
% 0.69/1.06      | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1335,plain,
% 0.69/1.06      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
% 0.69/1.06      | v4_pre_topc(sK2,sK0) != iProver_top
% 0.69/1.06      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | m1_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) != iProver_top
% 0.69/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK2)) = iProver_top ),
% 0.69/1.06      inference(superposition,[status(thm)],[c_2,c_962]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1336,plain,
% 0.69/1.06      ( v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
% 0.69/1.06      | v4_pre_topc(sK2,sK0) != iProver_top
% 0.69/1.06      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 0.69/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.69/1.06      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 0.69/1.06      inference(demodulation,[status(thm)],[c_1335,c_2]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_23,negated_conjecture,
% 0.69/1.06      ( ~ v2_struct_0(sK0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f59]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_24,plain,
% 0.69/1.06      ( v2_struct_0(sK0) != iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_26,plain,
% 0.69/1.06      ( l1_pre_topc(sK0) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_20,negated_conjecture,
% 0.69/1.06      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 0.69/1.06      inference(cnf_transformation,[],[f62]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_27,plain,
% 0.69/1.06      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_11,plain,
% 0.69/1.06      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 0.69/1.06      inference(cnf_transformation,[],[f55]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_61,plain,
% 0.69/1.06      ( v2_struct_0(X0) = iProver_top
% 0.69/1.06      | l1_struct_0(X0) != iProver_top
% 0.69/1.06      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_63,plain,
% 0.69/1.06      ( v2_struct_0(sK0) = iProver_top
% 0.69/1.06      | l1_struct_0(sK0) != iProver_top
% 0.69/1.06      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
% 0.69/1.06      inference(instantiation,[status(thm)],[c_61]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_10,plain,
% 0.69/1.06      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f54]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_64,plain,
% 0.69/1.06      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_66,plain,
% 0.69/1.06      ( l1_struct_0(sK0) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 0.69/1.06      inference(instantiation,[status(thm)],[c_64]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_0,negated_conjecture,
% 0.69/1.06      ( v1_xboole_0(sK2) ),
% 0.69/1.06      inference(cnf_transformation,[],[f71]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_8,plain,
% 0.69/1.06      ( v4_pre_topc(X0,X1)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.69/1.06      | ~ v2_pre_topc(X1)
% 0.69/1.06      | ~ l1_pre_topc(X1)
% 0.69/1.06      | ~ v1_xboole_0(X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f52]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_22,negated_conjecture,
% 0.69/1.06      ( v2_pre_topc(sK0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f60]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_314,plain,
% 0.69/1.06      ( v4_pre_topc(X0,X1)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.69/1.06      | ~ l1_pre_topc(X1)
% 0.69/1.06      | ~ v1_xboole_0(X0)
% 0.69/1.06      | sK0 != X1 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_315,plain,
% 0.69/1.06      ( v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ l1_pre_topc(sK0)
% 0.69/1.06      | ~ v1_xboole_0(X0) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_314]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_319,plain,
% 0.69/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ v1_xboole_0(X0) ),
% 0.69/1.06      inference(global_propositional_subsumption,[status(thm)],[c_315,c_21]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_320,plain,
% 0.69/1.06      ( v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | ~ v1_xboole_0(X0) ),
% 0.69/1.06      inference(renaming,[status(thm)],[c_319]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_385,plain,
% 0.69/1.06      ( v4_pre_topc(X0,sK0)
% 0.69/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.69/1.06      | sK2 != X0 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_320]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_386,plain,
% 0.69/1.06      ( v4_pre_topc(sK2,sK0)
% 0.69/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_385]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_4,negated_conjecture,
% 0.69/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 0.69/1.06      inference(cnf_transformation,[],[f75]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_392,plain,
% 0.69/1.06      ( v4_pre_topc(sK2,sK0) ),
% 0.69/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_386,c_4]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_394,plain,
% 0.69/1.06      ( v4_pre_topc(sK2,sK0) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_12,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(X0),X0)
% 0.69/1.06      | ~ v2_pre_topc(X0)
% 0.69/1.06      | ~ l1_pre_topc(X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f56]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_303,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_304,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_303]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_59,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(sK0),sK0)
% 0.69/1.06      | ~ v2_pre_topc(sK0)
% 0.69/1.06      | ~ l1_pre_topc(sK0) ),
% 0.69/1.06      inference(instantiation,[status(thm)],[c_12]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_306,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
% 0.69/1.06      inference(global_propositional_subsumption,
% 0.69/1.06                [status(thm)],
% 0.69/1.06                [c_304,c_22,c_21,c_59]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_965,plain,
% 0.69/1.06      ( v4_pre_topc(k2_struct_0(sK0),sK0) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_9,plain,
% 0.69/1.06      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 0.69/1.06      inference(cnf_transformation,[],[f53]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_289,plain,
% 0.69/1.06      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 0.69/1.06      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_341,plain,
% 0.69/1.06      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 0.69/1.06      inference(resolution_lifted,[status(thm)],[c_289,c_21]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_342,plain,
% 0.69/1.06      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 0.69/1.06      inference(unflattening,[status(thm)],[c_341]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_978,plain,
% 0.69/1.06      ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
% 0.69/1.06      inference(light_normalisation,[status(thm)],[c_965,c_342]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1218,plain,
% 0.69/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.69/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1219,plain,
% 0.69/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1339,plain,
% 0.69/1.06      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.69/1.06      inference(global_propositional_subsumption,
% 0.69/1.06                [status(thm)],
% 0.69/1.06                [c_1336,c_24,c_26,c_27,c_63,c_66,c_394,c_978,c_1219]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_3,negated_conjecture,
% 0.69/1.06      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
% 0.69/1.06      inference(cnf_transformation,[],[f74]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_970,plain,
% 0.69/1.06      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
% 0.69/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_987,plain,
% 0.69/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.69/1.06      inference(light_normalisation,[status(thm)],[c_970,c_2]) ).
% 0.69/1.06  
% 0.69/1.06  cnf(c_1344,plain,
% 0.69/1.06      ( $false ),
% 0.69/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_1339,c_987]) ).
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.69/1.06  
% 0.69/1.06  ------                               Statistics
% 0.69/1.06  
% 0.69/1.06  ------ General
% 0.69/1.06  
% 0.69/1.06  abstr_ref_over_cycles:                  0
% 0.69/1.06  abstr_ref_under_cycles:                 0
% 0.69/1.06  gc_basic_clause_elim:                   0
% 0.69/1.06  forced_gc_time:                         0
% 0.69/1.06  parsing_time:                           0.026
% 0.69/1.06  unif_index_cands_time:                  0.
% 0.69/1.06  unif_index_add_time:                    0.
% 0.69/1.06  orderings_time:                         0.
% 0.69/1.06  out_proof_time:                         0.011
% 0.69/1.06  total_time:                             0.095
% 0.69/1.06  num_of_symbols:                         48
% 0.69/1.06  num_of_terms:                           976
% 0.69/1.06  
% 0.69/1.06  ------ Preprocessing
% 0.69/1.06  
% 0.69/1.06  num_of_splits:                          0
% 0.69/1.06  num_of_split_atoms:                     0
% 0.69/1.06  num_of_reused_defs:                     0
% 0.69/1.06  num_eq_ax_congr_red:                    3
% 0.69/1.06  num_of_sem_filtered_clauses:            1
% 0.69/1.06  num_of_subtypes:                        0
% 0.69/1.06  monotx_restored_types:                  0
% 0.69/1.06  sat_num_of_epr_types:                   0
% 0.69/1.06  sat_num_of_non_cyclic_types:            0
% 0.69/1.06  sat_guarded_non_collapsed_types:        0
% 0.69/1.06  num_pure_diseq_elim:                    0
% 0.69/1.06  simp_replaced_by:                       0
% 0.69/1.06  res_preprocessed:                       79
% 0.69/1.06  prep_upred:                             0
% 0.69/1.06  prep_unflattend:                        24
% 0.69/1.06  smt_new_axioms:                         0
% 0.69/1.06  pred_elim_cands:                        3
% 0.69/1.06  pred_elim:                              7
% 0.69/1.06  pred_elim_cl:                           12
% 0.69/1.06  pred_elim_cycles:                       10
% 0.69/1.06  merged_defs:                            0
% 0.69/1.06  merged_defs_ncl:                        0
% 0.69/1.06  bin_hyper_res:                          0
% 0.69/1.06  prep_cycles:                            4
% 0.69/1.06  pred_elim_time:                         0.007
% 0.69/1.06  splitting_time:                         0.
% 0.69/1.06  sem_filter_time:                        0.
% 0.69/1.06  monotx_time:                            0.
% 0.69/1.06  subtype_inf_time:                       0.
% 0.69/1.06  
% 0.69/1.06  ------ Problem properties
% 0.69/1.06  
% 0.69/1.06  clauses:                                12
% 0.69/1.06  conjectures:                            6
% 0.69/1.06  epr:                                    1
% 0.69/1.06  horn:                                   11
% 0.69/1.06  ground:                                 6
% 0.69/1.06  unary:                                  9
% 0.69/1.06  binary:                                 0
% 0.69/1.06  lits:                                   22
% 0.69/1.06  lits_eq:                                2
% 0.69/1.06  fd_pure:                                0
% 0.69/1.06  fd_pseudo:                              0
% 0.69/1.06  fd_cond:                                0
% 0.69/1.06  fd_pseudo_cond:                         0
% 0.69/1.06  ac_symbols:                             0
% 0.69/1.06  
% 0.69/1.06  ------ Propositional Solver
% 0.69/1.06  
% 0.69/1.06  prop_solver_calls:                      24
% 0.69/1.06  prop_fast_solver_calls:                 444
% 0.69/1.06  smt_solver_calls:                       0
% 0.69/1.06  smt_fast_solver_calls:                  0
% 0.69/1.06  prop_num_of_clauses:                    358
% 0.69/1.06  prop_preprocess_simplified:             2124
% 0.69/1.06  prop_fo_subsumed:                       10
% 0.69/1.06  prop_solver_time:                       0.
% 0.69/1.06  smt_solver_time:                        0.
% 0.69/1.06  smt_fast_solver_time:                   0.
% 0.69/1.06  prop_fast_solver_time:                  0.
% 0.69/1.06  prop_unsat_core_time:                   0.
% 0.69/1.06  
% 0.69/1.06  ------ QBF
% 0.69/1.06  
% 0.69/1.06  qbf_q_res:                              0
% 0.69/1.06  qbf_num_tautologies:                    0
% 0.69/1.06  qbf_prep_cycles:                        0
% 0.69/1.06  
% 0.69/1.06  ------ BMC1
% 0.69/1.06  
% 0.69/1.06  bmc1_current_bound:                     -1
% 0.69/1.06  bmc1_last_solved_bound:                 -1
% 0.69/1.06  bmc1_unsat_core_size:                   -1
% 0.69/1.06  bmc1_unsat_core_parents_size:           -1
% 0.69/1.06  bmc1_merge_next_fun:                    0
% 0.69/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.69/1.06  
% 0.69/1.06  ------ Instantiation
% 0.69/1.06  
% 0.69/1.06  inst_num_of_clauses:                    92
% 0.69/1.06  inst_num_in_passive:                    0
% 0.69/1.06  inst_num_in_active:                     49
% 0.69/1.06  inst_num_in_unprocessed:                43
% 0.69/1.06  inst_num_of_loops:                      50
% 0.69/1.06  inst_num_of_learning_restarts:          0
% 0.69/1.06  inst_num_moves_active_passive:          0
% 0.69/1.06  inst_lit_activity:                      0
% 0.69/1.06  inst_lit_activity_moves:                0
% 0.69/1.06  inst_num_tautologies:                   0
% 0.69/1.06  inst_num_prop_implied:                  0
% 0.69/1.06  inst_num_existing_simplified:           0
% 0.69/1.06  inst_num_eq_res_simplified:             0
% 0.69/1.06  inst_num_child_elim:                    0
% 0.69/1.06  inst_num_of_dismatching_blockings:      2
% 0.69/1.06  inst_num_of_non_proper_insts:           49
% 0.69/1.06  inst_num_of_duplicates:                 0
% 0.69/1.06  inst_inst_num_from_inst_to_res:         0
% 0.69/1.06  inst_dismatching_checking_time:         0.
% 0.69/1.06  
% 0.69/1.06  ------ Resolution
% 0.69/1.06  
% 0.69/1.06  res_num_of_clauses:                     0
% 0.69/1.06  res_num_in_passive:                     0
% 0.69/1.06  res_num_in_active:                      0
% 0.69/1.06  res_num_of_loops:                       83
% 0.69/1.06  res_forward_subset_subsumed:            8
% 0.69/1.06  res_backward_subset_subsumed:           1
% 0.69/1.06  res_forward_subsumed:                   0
% 0.69/1.06  res_backward_subsumed:                  2
% 0.69/1.06  res_forward_subsumption_resolution:     1
% 0.69/1.06  res_backward_subsumption_resolution:    1
% 0.69/1.06  res_clause_to_clause_subsumption:       33
% 0.69/1.06  res_orphan_elimination:                 0
% 0.69/1.06  res_tautology_del:                      9
% 0.69/1.06  res_num_eq_res_simplified:              0
% 0.69/1.06  res_num_sel_changes:                    0
% 0.69/1.06  res_moves_from_active_to_pass:          0
% 0.69/1.06  
% 0.69/1.06  ------ Superposition
% 0.69/1.06  
% 0.69/1.06  sup_time_total:                         0.
% 0.69/1.06  sup_time_generating:                    0.
% 0.69/1.06  sup_time_sim_full:                      0.
% 0.69/1.06  sup_time_sim_immed:                     0.
% 0.69/1.06  
% 0.69/1.06  sup_num_of_clauses:                     11
% 0.69/1.06  sup_num_in_active:                      9
% 0.69/1.06  sup_num_in_passive:                     2
% 0.69/1.06  sup_num_of_loops:                       9
% 0.69/1.06  sup_fw_superposition:                   1
% 0.69/1.06  sup_bw_superposition:                   0
% 0.69/1.06  sup_immediate_simplified:               1
% 0.69/1.06  sup_given_eliminated:                   0
% 0.69/1.06  comparisons_done:                       0
% 0.69/1.06  comparisons_avoided:                    0
% 0.69/1.06  
% 0.69/1.06  ------ Simplifications
% 0.69/1.06  
% 0.69/1.06  
% 0.69/1.06  sim_fw_subset_subsumed:                 0
% 0.69/1.06  sim_bw_subset_subsumed:                 0
% 0.69/1.06  sim_fw_subsumed:                        1
% 0.69/1.06  sim_bw_subsumed:                        0
% 0.69/1.06  sim_fw_subsumption_res:                 1
% 0.69/1.06  sim_bw_subsumption_res:                 0
% 0.69/1.06  sim_tautology_del:                      0
% 0.69/1.06  sim_eq_tautology_del:                   0
% 0.69/1.06  sim_eq_res_simp:                        0
% 0.69/1.06  sim_fw_demodulated:                     1
% 0.69/1.06  sim_bw_demodulated:                     0
% 0.69/1.06  sim_light_normalised:                   2
% 0.69/1.06  sim_joinable_taut:                      0
% 0.69/1.06  sim_joinable_simp:                      0
% 0.69/1.06  sim_ac_normalised:                      0
% 0.69/1.06  sim_smt_subsumption:                    0
% 0.69/1.06  
%------------------------------------------------------------------------------
