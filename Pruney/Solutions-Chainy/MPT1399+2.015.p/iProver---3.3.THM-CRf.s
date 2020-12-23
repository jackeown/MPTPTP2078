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
% DateTime   : Thu Dec  3 12:18:34 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 470 expanded)
%              Number of clauses        :   65 (  85 expanded)
%              Number of leaves         :   19 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  462 (4550 expanded)
%              Number of equality atoms :  100 ( 462 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
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

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f48,f68])).

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

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f49,f68])).

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

cnf(c_363,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_364,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_403,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ r2_hidden(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_364])).

cnf(c_404,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_698,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
    | r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1134,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_698])).

cnf(c_1135,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | r2_hidden(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1134,c_2])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

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

cnf(c_303,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_304,plain,
    ( v4_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_316,plain,
    ( v4_pre_topc(sK2,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_304,c_4])).

cnf(c_320,plain,
    ( v4_pre_topc(sK2,X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_322,plain,
    ( v4_pre_topc(sK2,sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_276,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_277,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_65,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_68,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_279,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_23,c_21,c_65,c_68])).

cnf(c_323,plain,
    ( u1_struct_0(sK0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_279])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_343,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_344,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_62,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_346,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_22,c_21,c_62])).

cnf(c_699,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_289,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_358,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_289,c_21])).

cnf(c_359,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_716,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_699,c_359])).

cnf(c_937,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_940,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_702,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK2 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_705,plain,
    ( sK2 = X0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_996,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_705])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1001,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_44])).

cnf(c_1002,plain,
    ( sK2 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1001])).

cnf(c_1012,plain,
    ( u1_struct_0(sK0) = sK2
    | r2_hidden(sK1,u1_struct_0(sK0)) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_1002])).

cnf(c_1215,plain,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1216,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_1233,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1135,c_25,c_26,c_322,c_323,c_716,c_940,c_1012,c_1216])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_707,plain,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_707,c_2])).

cnf(c_1238,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1233,c_725])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.53/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/0.96  
% 1.53/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/0.96  
% 1.53/0.96  ------  iProver source info
% 1.53/0.96  
% 1.53/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.53/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/0.96  git: non_committed_changes: false
% 1.53/0.96  git: last_make_outside_of_git: false
% 1.53/0.96  
% 1.53/0.96  ------ 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options
% 1.53/0.96  
% 1.53/0.96  --out_options                           all
% 1.53/0.96  --tptp_safe_out                         true
% 1.53/0.96  --problem_path                          ""
% 1.53/0.96  --include_path                          ""
% 1.53/0.96  --clausifier                            res/vclausify_rel
% 1.53/0.96  --clausifier_options                    --mode clausify
% 1.53/0.96  --stdin                                 false
% 1.53/0.96  --stats_out                             all
% 1.53/0.96  
% 1.53/0.96  ------ General Options
% 1.53/0.96  
% 1.53/0.96  --fof                                   false
% 1.53/0.96  --time_out_real                         305.
% 1.53/0.96  --time_out_virtual                      -1.
% 1.53/0.96  --symbol_type_check                     false
% 1.53/0.96  --clausify_out                          false
% 1.53/0.96  --sig_cnt_out                           false
% 1.53/0.96  --trig_cnt_out                          false
% 1.53/0.96  --trig_cnt_out_tolerance                1.
% 1.53/0.96  --trig_cnt_out_sk_spl                   false
% 1.53/0.96  --abstr_cl_out                          false
% 1.53/0.96  
% 1.53/0.96  ------ Global Options
% 1.53/0.96  
% 1.53/0.96  --schedule                              default
% 1.53/0.96  --add_important_lit                     false
% 1.53/0.96  --prop_solver_per_cl                    1000
% 1.53/0.96  --min_unsat_core                        false
% 1.53/0.96  --soft_assumptions                      false
% 1.53/0.96  --soft_lemma_size                       3
% 1.53/0.96  --prop_impl_unit_size                   0
% 1.53/0.96  --prop_impl_unit                        []
% 1.53/0.96  --share_sel_clauses                     true
% 1.53/0.96  --reset_solvers                         false
% 1.53/0.96  --bc_imp_inh                            [conj_cone]
% 1.53/0.96  --conj_cone_tolerance                   3.
% 1.53/0.96  --extra_neg_conj                        none
% 1.53/0.96  --large_theory_mode                     true
% 1.53/0.96  --prolific_symb_bound                   200
% 1.53/0.96  --lt_threshold                          2000
% 1.53/0.96  --clause_weak_htbl                      true
% 1.53/0.96  --gc_record_bc_elim                     false
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing Options
% 1.53/0.96  
% 1.53/0.96  --preprocessing_flag                    true
% 1.53/0.96  --time_out_prep_mult                    0.1
% 1.53/0.96  --splitting_mode                        input
% 1.53/0.96  --splitting_grd                         true
% 1.53/0.96  --splitting_cvd                         false
% 1.53/0.96  --splitting_cvd_svl                     false
% 1.53/0.96  --splitting_nvd                         32
% 1.53/0.96  --sub_typing                            true
% 1.53/0.96  --prep_gs_sim                           true
% 1.53/0.96  --prep_unflatten                        true
% 1.53/0.96  --prep_res_sim                          true
% 1.53/0.96  --prep_upred                            true
% 1.53/0.96  --prep_sem_filter                       exhaustive
% 1.53/0.96  --prep_sem_filter_out                   false
% 1.53/0.96  --pred_elim                             true
% 1.53/0.96  --res_sim_input                         true
% 1.53/0.96  --eq_ax_congr_red                       true
% 1.53/0.96  --pure_diseq_elim                       true
% 1.53/0.96  --brand_transform                       false
% 1.53/0.96  --non_eq_to_eq                          false
% 1.53/0.96  --prep_def_merge                        true
% 1.53/0.96  --prep_def_merge_prop_impl              false
% 1.53/0.96  --prep_def_merge_mbd                    true
% 1.53/0.96  --prep_def_merge_tr_red                 false
% 1.53/0.96  --prep_def_merge_tr_cl                  false
% 1.53/0.96  --smt_preprocessing                     true
% 1.53/0.96  --smt_ac_axioms                         fast
% 1.53/0.96  --preprocessed_out                      false
% 1.53/0.96  --preprocessed_stats                    false
% 1.53/0.96  
% 1.53/0.96  ------ Abstraction refinement Options
% 1.53/0.96  
% 1.53/0.96  --abstr_ref                             []
% 1.53/0.96  --abstr_ref_prep                        false
% 1.53/0.96  --abstr_ref_until_sat                   false
% 1.53/0.96  --abstr_ref_sig_restrict                funpre
% 1.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.96  --abstr_ref_under                       []
% 1.53/0.96  
% 1.53/0.96  ------ SAT Options
% 1.53/0.96  
% 1.53/0.96  --sat_mode                              false
% 1.53/0.96  --sat_fm_restart_options                ""
% 1.53/0.96  --sat_gr_def                            false
% 1.53/0.96  --sat_epr_types                         true
% 1.53/0.96  --sat_non_cyclic_types                  false
% 1.53/0.96  --sat_finite_models                     false
% 1.53/0.96  --sat_fm_lemmas                         false
% 1.53/0.96  --sat_fm_prep                           false
% 1.53/0.96  --sat_fm_uc_incr                        true
% 1.53/0.96  --sat_out_model                         small
% 1.53/0.96  --sat_out_clauses                       false
% 1.53/0.96  
% 1.53/0.96  ------ QBF Options
% 1.53/0.96  
% 1.53/0.96  --qbf_mode                              false
% 1.53/0.96  --qbf_elim_univ                         false
% 1.53/0.96  --qbf_dom_inst                          none
% 1.53/0.96  --qbf_dom_pre_inst                      false
% 1.53/0.96  --qbf_sk_in                             false
% 1.53/0.96  --qbf_pred_elim                         true
% 1.53/0.96  --qbf_split                             512
% 1.53/0.96  
% 1.53/0.96  ------ BMC1 Options
% 1.53/0.96  
% 1.53/0.96  --bmc1_incremental                      false
% 1.53/0.96  --bmc1_axioms                           reachable_all
% 1.53/0.96  --bmc1_min_bound                        0
% 1.53/0.96  --bmc1_max_bound                        -1
% 1.53/0.96  --bmc1_max_bound_default                -1
% 1.53/0.96  --bmc1_symbol_reachability              true
% 1.53/0.96  --bmc1_property_lemmas                  false
% 1.53/0.96  --bmc1_k_induction                      false
% 1.53/0.96  --bmc1_non_equiv_states                 false
% 1.53/0.96  --bmc1_deadlock                         false
% 1.53/0.96  --bmc1_ucm                              false
% 1.53/0.96  --bmc1_add_unsat_core                   none
% 1.53/0.96  --bmc1_unsat_core_children              false
% 1.53/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.96  --bmc1_out_stat                         full
% 1.53/0.96  --bmc1_ground_init                      false
% 1.53/0.96  --bmc1_pre_inst_next_state              false
% 1.53/0.96  --bmc1_pre_inst_state                   false
% 1.53/0.96  --bmc1_pre_inst_reach_state             false
% 1.53/0.96  --bmc1_out_unsat_core                   false
% 1.53/0.96  --bmc1_aig_witness_out                  false
% 1.53/0.96  --bmc1_verbose                          false
% 1.53/0.96  --bmc1_dump_clauses_tptp                false
% 1.53/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.96  --bmc1_dump_file                        -
% 1.53/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.96  --bmc1_ucm_extend_mode                  1
% 1.53/0.96  --bmc1_ucm_init_mode                    2
% 1.53/0.96  --bmc1_ucm_cone_mode                    none
% 1.53/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.96  --bmc1_ucm_relax_model                  4
% 1.53/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.96  --bmc1_ucm_layered_model                none
% 1.53/0.96  --bmc1_ucm_max_lemma_size               10
% 1.53/0.96  
% 1.53/0.96  ------ AIG Options
% 1.53/0.96  
% 1.53/0.96  --aig_mode                              false
% 1.53/0.96  
% 1.53/0.96  ------ Instantiation Options
% 1.53/0.96  
% 1.53/0.96  --instantiation_flag                    true
% 1.53/0.96  --inst_sos_flag                         false
% 1.53/0.96  --inst_sos_phase                        true
% 1.53/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel_side                     num_symb
% 1.53/0.96  --inst_solver_per_active                1400
% 1.53/0.96  --inst_solver_calls_frac                1.
% 1.53/0.96  --inst_passive_queue_type               priority_queues
% 1.53/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.96  --inst_passive_queues_freq              [25;2]
% 1.53/0.96  --inst_dismatching                      true
% 1.53/0.96  --inst_eager_unprocessed_to_passive     true
% 1.53/0.96  --inst_prop_sim_given                   true
% 1.53/0.96  --inst_prop_sim_new                     false
% 1.53/0.96  --inst_subs_new                         false
% 1.53/0.96  --inst_eq_res_simp                      false
% 1.53/0.96  --inst_subs_given                       false
% 1.53/0.96  --inst_orphan_elimination               true
% 1.53/0.96  --inst_learning_loop_flag               true
% 1.53/0.96  --inst_learning_start                   3000
% 1.53/0.96  --inst_learning_factor                  2
% 1.53/0.96  --inst_start_prop_sim_after_learn       3
% 1.53/0.96  --inst_sel_renew                        solver
% 1.53/0.96  --inst_lit_activity_flag                true
% 1.53/0.96  --inst_restr_to_given                   false
% 1.53/0.96  --inst_activity_threshold               500
% 1.53/0.96  --inst_out_proof                        true
% 1.53/0.96  
% 1.53/0.96  ------ Resolution Options
% 1.53/0.96  
% 1.53/0.96  --resolution_flag                       true
% 1.53/0.96  --res_lit_sel                           adaptive
% 1.53/0.96  --res_lit_sel_side                      none
% 1.53/0.96  --res_ordering                          kbo
% 1.53/0.96  --res_to_prop_solver                    active
% 1.53/0.96  --res_prop_simpl_new                    false
% 1.53/0.96  --res_prop_simpl_given                  true
% 1.53/0.96  --res_passive_queue_type                priority_queues
% 1.53/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.96  --res_passive_queues_freq               [15;5]
% 1.53/0.96  --res_forward_subs                      full
% 1.53/0.96  --res_backward_subs                     full
% 1.53/0.96  --res_forward_subs_resolution           true
% 1.53/0.96  --res_backward_subs_resolution          true
% 1.53/0.96  --res_orphan_elimination                true
% 1.53/0.96  --res_time_limit                        2.
% 1.53/0.96  --res_out_proof                         true
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Options
% 1.53/0.96  
% 1.53/0.96  --superposition_flag                    true
% 1.53/0.96  --sup_passive_queue_type                priority_queues
% 1.53/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.96  --demod_completeness_check              fast
% 1.53/0.96  --demod_use_ground                      true
% 1.53/0.96  --sup_to_prop_solver                    passive
% 1.53/0.96  --sup_prop_simpl_new                    true
% 1.53/0.96  --sup_prop_simpl_given                  true
% 1.53/0.96  --sup_fun_splitting                     false
% 1.53/0.96  --sup_smt_interval                      50000
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Simplification Setup
% 1.53/0.96  
% 1.53/0.96  --sup_indices_passive                   []
% 1.53/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_full_bw                           [BwDemod]
% 1.53/0.96  --sup_immed_triv                        [TrivRules]
% 1.53/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_immed_bw_main                     []
% 1.53/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  
% 1.53/0.96  ------ Combination Options
% 1.53/0.96  
% 1.53/0.96  --comb_res_mult                         3
% 1.53/0.96  --comb_sup_mult                         2
% 1.53/0.96  --comb_inst_mult                        10
% 1.53/0.96  
% 1.53/0.96  ------ Debug Options
% 1.53/0.96  
% 1.53/0.96  --dbg_backtrace                         false
% 1.53/0.96  --dbg_dump_prop_clauses                 false
% 1.53/0.96  --dbg_dump_prop_clauses_file            -
% 1.53/0.96  --dbg_out_stat                          false
% 1.53/0.96  ------ Parsing...
% 1.53/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.53/0.96  ------ Proving...
% 1.53/0.96  ------ Problem Properties 
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  clauses                                 13
% 1.53/0.96  conjectures                             6
% 1.53/0.96  EPR                                     2
% 1.53/0.96  Horn                                    12
% 1.53/0.96  unary                                   10
% 1.53/0.96  binary                                  0
% 1.53/0.96  lits                                    23
% 1.53/0.96  lits eq                                 4
% 1.53/0.96  fd_pure                                 0
% 1.53/0.96  fd_pseudo                               0
% 1.53/0.96  fd_cond                                 1
% 1.53/0.96  fd_pseudo_cond                          0
% 1.53/0.96  AC symbols                              0
% 1.53/0.96  
% 1.53/0.96  ------ Schedule dynamic 5 is on 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  ------ 
% 1.53/0.96  Current options:
% 1.53/0.96  ------ 
% 1.53/0.96  
% 1.53/0.96  ------ Input Options
% 1.53/0.96  
% 1.53/0.96  --out_options                           all
% 1.53/0.96  --tptp_safe_out                         true
% 1.53/0.96  --problem_path                          ""
% 1.53/0.96  --include_path                          ""
% 1.53/0.96  --clausifier                            res/vclausify_rel
% 1.53/0.96  --clausifier_options                    --mode clausify
% 1.53/0.96  --stdin                                 false
% 1.53/0.96  --stats_out                             all
% 1.53/0.96  
% 1.53/0.96  ------ General Options
% 1.53/0.96  
% 1.53/0.96  --fof                                   false
% 1.53/0.96  --time_out_real                         305.
% 1.53/0.96  --time_out_virtual                      -1.
% 1.53/0.96  --symbol_type_check                     false
% 1.53/0.96  --clausify_out                          false
% 1.53/0.96  --sig_cnt_out                           false
% 1.53/0.96  --trig_cnt_out                          false
% 1.53/0.96  --trig_cnt_out_tolerance                1.
% 1.53/0.96  --trig_cnt_out_sk_spl                   false
% 1.53/0.96  --abstr_cl_out                          false
% 1.53/0.96  
% 1.53/0.96  ------ Global Options
% 1.53/0.96  
% 1.53/0.96  --schedule                              default
% 1.53/0.96  --add_important_lit                     false
% 1.53/0.96  --prop_solver_per_cl                    1000
% 1.53/0.96  --min_unsat_core                        false
% 1.53/0.96  --soft_assumptions                      false
% 1.53/0.96  --soft_lemma_size                       3
% 1.53/0.96  --prop_impl_unit_size                   0
% 1.53/0.96  --prop_impl_unit                        []
% 1.53/0.96  --share_sel_clauses                     true
% 1.53/0.96  --reset_solvers                         false
% 1.53/0.96  --bc_imp_inh                            [conj_cone]
% 1.53/0.96  --conj_cone_tolerance                   3.
% 1.53/0.96  --extra_neg_conj                        none
% 1.53/0.96  --large_theory_mode                     true
% 1.53/0.96  --prolific_symb_bound                   200
% 1.53/0.96  --lt_threshold                          2000
% 1.53/0.96  --clause_weak_htbl                      true
% 1.53/0.96  --gc_record_bc_elim                     false
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing Options
% 1.53/0.96  
% 1.53/0.96  --preprocessing_flag                    true
% 1.53/0.96  --time_out_prep_mult                    0.1
% 1.53/0.96  --splitting_mode                        input
% 1.53/0.96  --splitting_grd                         true
% 1.53/0.96  --splitting_cvd                         false
% 1.53/0.96  --splitting_cvd_svl                     false
% 1.53/0.96  --splitting_nvd                         32
% 1.53/0.96  --sub_typing                            true
% 1.53/0.96  --prep_gs_sim                           true
% 1.53/0.96  --prep_unflatten                        true
% 1.53/0.96  --prep_res_sim                          true
% 1.53/0.96  --prep_upred                            true
% 1.53/0.96  --prep_sem_filter                       exhaustive
% 1.53/0.96  --prep_sem_filter_out                   false
% 1.53/0.96  --pred_elim                             true
% 1.53/0.96  --res_sim_input                         true
% 1.53/0.96  --eq_ax_congr_red                       true
% 1.53/0.96  --pure_diseq_elim                       true
% 1.53/0.96  --brand_transform                       false
% 1.53/0.96  --non_eq_to_eq                          false
% 1.53/0.96  --prep_def_merge                        true
% 1.53/0.96  --prep_def_merge_prop_impl              false
% 1.53/0.96  --prep_def_merge_mbd                    true
% 1.53/0.96  --prep_def_merge_tr_red                 false
% 1.53/0.96  --prep_def_merge_tr_cl                  false
% 1.53/0.96  --smt_preprocessing                     true
% 1.53/0.96  --smt_ac_axioms                         fast
% 1.53/0.96  --preprocessed_out                      false
% 1.53/0.96  --preprocessed_stats                    false
% 1.53/0.96  
% 1.53/0.96  ------ Abstraction refinement Options
% 1.53/0.96  
% 1.53/0.96  --abstr_ref                             []
% 1.53/0.96  --abstr_ref_prep                        false
% 1.53/0.96  --abstr_ref_until_sat                   false
% 1.53/0.96  --abstr_ref_sig_restrict                funpre
% 1.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.96  --abstr_ref_under                       []
% 1.53/0.96  
% 1.53/0.96  ------ SAT Options
% 1.53/0.96  
% 1.53/0.96  --sat_mode                              false
% 1.53/0.96  --sat_fm_restart_options                ""
% 1.53/0.96  --sat_gr_def                            false
% 1.53/0.96  --sat_epr_types                         true
% 1.53/0.96  --sat_non_cyclic_types                  false
% 1.53/0.96  --sat_finite_models                     false
% 1.53/0.96  --sat_fm_lemmas                         false
% 1.53/0.96  --sat_fm_prep                           false
% 1.53/0.96  --sat_fm_uc_incr                        true
% 1.53/0.96  --sat_out_model                         small
% 1.53/0.96  --sat_out_clauses                       false
% 1.53/0.96  
% 1.53/0.96  ------ QBF Options
% 1.53/0.96  
% 1.53/0.96  --qbf_mode                              false
% 1.53/0.96  --qbf_elim_univ                         false
% 1.53/0.96  --qbf_dom_inst                          none
% 1.53/0.96  --qbf_dom_pre_inst                      false
% 1.53/0.96  --qbf_sk_in                             false
% 1.53/0.96  --qbf_pred_elim                         true
% 1.53/0.96  --qbf_split                             512
% 1.53/0.96  
% 1.53/0.96  ------ BMC1 Options
% 1.53/0.96  
% 1.53/0.96  --bmc1_incremental                      false
% 1.53/0.96  --bmc1_axioms                           reachable_all
% 1.53/0.96  --bmc1_min_bound                        0
% 1.53/0.96  --bmc1_max_bound                        -1
% 1.53/0.96  --bmc1_max_bound_default                -1
% 1.53/0.96  --bmc1_symbol_reachability              true
% 1.53/0.96  --bmc1_property_lemmas                  false
% 1.53/0.96  --bmc1_k_induction                      false
% 1.53/0.96  --bmc1_non_equiv_states                 false
% 1.53/0.96  --bmc1_deadlock                         false
% 1.53/0.96  --bmc1_ucm                              false
% 1.53/0.96  --bmc1_add_unsat_core                   none
% 1.53/0.96  --bmc1_unsat_core_children              false
% 1.53/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.96  --bmc1_out_stat                         full
% 1.53/0.96  --bmc1_ground_init                      false
% 1.53/0.96  --bmc1_pre_inst_next_state              false
% 1.53/0.96  --bmc1_pre_inst_state                   false
% 1.53/0.96  --bmc1_pre_inst_reach_state             false
% 1.53/0.96  --bmc1_out_unsat_core                   false
% 1.53/0.96  --bmc1_aig_witness_out                  false
% 1.53/0.96  --bmc1_verbose                          false
% 1.53/0.96  --bmc1_dump_clauses_tptp                false
% 1.53/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.96  --bmc1_dump_file                        -
% 1.53/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.96  --bmc1_ucm_extend_mode                  1
% 1.53/0.96  --bmc1_ucm_init_mode                    2
% 1.53/0.96  --bmc1_ucm_cone_mode                    none
% 1.53/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.96  --bmc1_ucm_relax_model                  4
% 1.53/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.96  --bmc1_ucm_layered_model                none
% 1.53/0.96  --bmc1_ucm_max_lemma_size               10
% 1.53/0.96  
% 1.53/0.96  ------ AIG Options
% 1.53/0.96  
% 1.53/0.96  --aig_mode                              false
% 1.53/0.96  
% 1.53/0.96  ------ Instantiation Options
% 1.53/0.96  
% 1.53/0.96  --instantiation_flag                    true
% 1.53/0.96  --inst_sos_flag                         false
% 1.53/0.96  --inst_sos_phase                        true
% 1.53/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.96  --inst_lit_sel_side                     none
% 1.53/0.96  --inst_solver_per_active                1400
% 1.53/0.96  --inst_solver_calls_frac                1.
% 1.53/0.96  --inst_passive_queue_type               priority_queues
% 1.53/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.96  --inst_passive_queues_freq              [25;2]
% 1.53/0.96  --inst_dismatching                      true
% 1.53/0.96  --inst_eager_unprocessed_to_passive     true
% 1.53/0.96  --inst_prop_sim_given                   true
% 1.53/0.96  --inst_prop_sim_new                     false
% 1.53/0.96  --inst_subs_new                         false
% 1.53/0.96  --inst_eq_res_simp                      false
% 1.53/0.96  --inst_subs_given                       false
% 1.53/0.96  --inst_orphan_elimination               true
% 1.53/0.96  --inst_learning_loop_flag               true
% 1.53/0.96  --inst_learning_start                   3000
% 1.53/0.96  --inst_learning_factor                  2
% 1.53/0.96  --inst_start_prop_sim_after_learn       3
% 1.53/0.96  --inst_sel_renew                        solver
% 1.53/0.96  --inst_lit_activity_flag                true
% 1.53/0.96  --inst_restr_to_given                   false
% 1.53/0.96  --inst_activity_threshold               500
% 1.53/0.96  --inst_out_proof                        true
% 1.53/0.96  
% 1.53/0.96  ------ Resolution Options
% 1.53/0.96  
% 1.53/0.96  --resolution_flag                       false
% 1.53/0.96  --res_lit_sel                           adaptive
% 1.53/0.96  --res_lit_sel_side                      none
% 1.53/0.96  --res_ordering                          kbo
% 1.53/0.96  --res_to_prop_solver                    active
% 1.53/0.96  --res_prop_simpl_new                    false
% 1.53/0.96  --res_prop_simpl_given                  true
% 1.53/0.96  --res_passive_queue_type                priority_queues
% 1.53/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.96  --res_passive_queues_freq               [15;5]
% 1.53/0.96  --res_forward_subs                      full
% 1.53/0.96  --res_backward_subs                     full
% 1.53/0.96  --res_forward_subs_resolution           true
% 1.53/0.96  --res_backward_subs_resolution          true
% 1.53/0.96  --res_orphan_elimination                true
% 1.53/0.96  --res_time_limit                        2.
% 1.53/0.96  --res_out_proof                         true
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Options
% 1.53/0.96  
% 1.53/0.96  --superposition_flag                    true
% 1.53/0.96  --sup_passive_queue_type                priority_queues
% 1.53/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.96  --demod_completeness_check              fast
% 1.53/0.96  --demod_use_ground                      true
% 1.53/0.96  --sup_to_prop_solver                    passive
% 1.53/0.96  --sup_prop_simpl_new                    true
% 1.53/0.96  --sup_prop_simpl_given                  true
% 1.53/0.96  --sup_fun_splitting                     false
% 1.53/0.96  --sup_smt_interval                      50000
% 1.53/0.96  
% 1.53/0.96  ------ Superposition Simplification Setup
% 1.53/0.96  
% 1.53/0.96  --sup_indices_passive                   []
% 1.53/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_full_bw                           [BwDemod]
% 1.53/0.96  --sup_immed_triv                        [TrivRules]
% 1.53/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_immed_bw_main                     []
% 1.53/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.96  
% 1.53/0.96  ------ Combination Options
% 1.53/0.96  
% 1.53/0.96  --comb_res_mult                         3
% 1.53/0.96  --comb_sup_mult                         2
% 1.53/0.96  --comb_inst_mult                        10
% 1.53/0.96  
% 1.53/0.96  ------ Debug Options
% 1.53/0.96  
% 1.53/0.96  --dbg_backtrace                         false
% 1.53/0.96  --dbg_dump_prop_clauses                 false
% 1.53/0.96  --dbg_dump_prop_clauses_file            -
% 1.53/0.96  --dbg_out_stat                          false
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  ------ Proving...
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  % SZS status Theorem for theBenchmark.p
% 1.53/0.96  
% 1.53/0.96   Resolution empty clause
% 1.53/0.96  
% 1.53/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.53/0.96  
% 1.53/0.96  fof(f4,axiom,(
% 1.53/0.96    ! [X0] : k2_subset_1(X0) = X0),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f45,plain,(
% 1.53/0.96    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.53/0.96    inference(cnf_transformation,[],[f4])).
% 1.53/0.96  
% 1.53/0.96  fof(f6,axiom,(
% 1.53/0.96    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f47,plain,(
% 1.53/0.96    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.53/0.96    inference(cnf_transformation,[],[f6])).
% 1.53/0.96  
% 1.53/0.96  fof(f3,axiom,(
% 1.53/0.96    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f44,plain,(
% 1.53/0.96    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f3])).
% 1.53/0.96  
% 1.53/0.96  fof(f17,conjecture,(
% 1.53/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f18,negated_conjecture,(
% 1.53/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.53/0.96    inference(negated_conjecture,[],[f17])).
% 1.53/0.96  
% 1.53/0.96  fof(f33,plain,(
% 1.53/0.96    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.96    inference(ennf_transformation,[],[f18])).
% 1.53/0.96  
% 1.53/0.96  fof(f34,plain,(
% 1.53/0.96    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.96    inference(flattening,[],[f33])).
% 1.53/0.96  
% 1.53/0.96  fof(f36,plain,(
% 1.53/0.96    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.96    inference(nnf_transformation,[],[f34])).
% 1.53/0.96  
% 1.53/0.96  fof(f37,plain,(
% 1.53/0.96    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.96    inference(flattening,[],[f36])).
% 1.53/0.96  
% 1.53/0.96  fof(f40,plain,(
% 1.53/0.96    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.53/0.96    introduced(choice_axiom,[])).
% 1.53/0.96  
% 1.53/0.96  fof(f39,plain,(
% 1.53/0.96    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.53/0.96    introduced(choice_axiom,[])).
% 1.53/0.96  
% 1.53/0.96  fof(f38,plain,(
% 1.53/0.96    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.53/0.96    introduced(choice_axiom,[])).
% 1.53/0.96  
% 1.53/0.96  fof(f41,plain,(
% 1.53/0.96    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.53/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 1.53/0.96  
% 1.53/0.96  fof(f68,plain,(
% 1.53/0.96    k1_xboole_0 = sK2),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f69,plain,(
% 1.53/0.96    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 1.53/0.96    inference(definition_unfolding,[],[f44,f68])).
% 1.53/0.96  
% 1.53/0.96  fof(f70,plain,(
% 1.53/0.96    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 1.53/0.96    inference(definition_unfolding,[],[f47,f69])).
% 1.53/0.96  
% 1.53/0.96  fof(f73,plain,(
% 1.53/0.96    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 1.53/0.96    inference(definition_unfolding,[],[f45,f70])).
% 1.53/0.96  
% 1.53/0.96  fof(f2,axiom,(
% 1.53/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f43,plain,(
% 1.53/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f2])).
% 1.53/0.96  
% 1.53/0.96  fof(f72,plain,(
% 1.53/0.96    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 1.53/0.96    inference(definition_unfolding,[],[f43,f68])).
% 1.53/0.96  
% 1.53/0.96  fof(f10,axiom,(
% 1.53/0.96    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f23,plain,(
% 1.53/0.96    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.53/0.96    inference(ennf_transformation,[],[f10])).
% 1.53/0.96  
% 1.53/0.96  fof(f51,plain,(
% 1.53/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f23])).
% 1.53/0.96  
% 1.53/0.96  fof(f67,plain,(
% 1.53/0.96    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f16,axiom,(
% 1.53/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f32,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.96    inference(ennf_transformation,[],[f16])).
% 1.53/0.96  
% 1.53/0.96  fof(f35,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.96    inference(nnf_transformation,[],[f32])).
% 1.53/0.96  
% 1.53/0.96  fof(f57,plain,(
% 1.53/0.96    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f35])).
% 1.53/0.96  
% 1.53/0.96  fof(f61,plain,(
% 1.53/0.96    l1_pre_topc(sK0)),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f60,plain,(
% 1.53/0.96    v2_pre_topc(sK0)),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f1,axiom,(
% 1.53/0.96    v1_xboole_0(k1_xboole_0)),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f42,plain,(
% 1.53/0.96    v1_xboole_0(k1_xboole_0)),
% 1.53/0.96    inference(cnf_transformation,[],[f1])).
% 1.53/0.96  
% 1.53/0.96  fof(f71,plain,(
% 1.53/0.96    v1_xboole_0(sK2)),
% 1.53/0.96    inference(definition_unfolding,[],[f42,f68])).
% 1.53/0.96  
% 1.53/0.96  fof(f11,axiom,(
% 1.53/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f24,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.96    inference(ennf_transformation,[],[f11])).
% 1.53/0.96  
% 1.53/0.96  fof(f25,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.96    inference(flattening,[],[f24])).
% 1.53/0.96  
% 1.53/0.96  fof(f52,plain,(
% 1.53/0.96    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f25])).
% 1.53/0.96  
% 1.53/0.96  fof(f7,axiom,(
% 1.53/0.96    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f48,plain,(
% 1.53/0.96    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.53/0.96    inference(cnf_transformation,[],[f7])).
% 1.53/0.96  
% 1.53/0.96  fof(f75,plain,(
% 1.53/0.96    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.53/0.96    inference(definition_unfolding,[],[f48,f68])).
% 1.53/0.96  
% 1.53/0.96  fof(f14,axiom,(
% 1.53/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f28,plain,(
% 1.53/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.96    inference(ennf_transformation,[],[f14])).
% 1.53/0.96  
% 1.53/0.96  fof(f29,plain,(
% 1.53/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.96    inference(flattening,[],[f28])).
% 1.53/0.96  
% 1.53/0.96  fof(f55,plain,(
% 1.53/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f29])).
% 1.53/0.96  
% 1.53/0.96  fof(f59,plain,(
% 1.53/0.96    ~v2_struct_0(sK0)),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f13,axiom,(
% 1.53/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f27,plain,(
% 1.53/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.96    inference(ennf_transformation,[],[f13])).
% 1.53/0.96  
% 1.53/0.96  fof(f54,plain,(
% 1.53/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f27])).
% 1.53/0.96  
% 1.53/0.96  fof(f15,axiom,(
% 1.53/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f30,plain,(
% 1.53/0.96    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.96    inference(ennf_transformation,[],[f15])).
% 1.53/0.96  
% 1.53/0.96  fof(f31,plain,(
% 1.53/0.96    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.96    inference(flattening,[],[f30])).
% 1.53/0.96  
% 1.53/0.96  fof(f56,plain,(
% 1.53/0.96    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f31])).
% 1.53/0.96  
% 1.53/0.96  fof(f12,axiom,(
% 1.53/0.96    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f26,plain,(
% 1.53/0.96    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.53/0.96    inference(ennf_transformation,[],[f12])).
% 1.53/0.96  
% 1.53/0.96  fof(f53,plain,(
% 1.53/0.96    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.53/0.96    inference(cnf_transformation,[],[f26])).
% 1.53/0.96  
% 1.53/0.96  fof(f62,plain,(
% 1.53/0.96    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.53/0.96    inference(cnf_transformation,[],[f41])).
% 1.53/0.96  
% 1.53/0.96  fof(f8,axiom,(
% 1.53/0.96    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f19,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.53/0.96    inference(ennf_transformation,[],[f8])).
% 1.53/0.96  
% 1.53/0.96  fof(f20,plain,(
% 1.53/0.96    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.53/0.96    inference(flattening,[],[f19])).
% 1.53/0.96  
% 1.53/0.96  fof(f49,plain,(
% 1.53/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 1.53/0.96    inference(cnf_transformation,[],[f20])).
% 1.53/0.96  
% 1.53/0.96  fof(f76,plain,(
% 1.53/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 1.53/0.96    inference(definition_unfolding,[],[f49,f68])).
% 1.53/0.96  
% 1.53/0.96  fof(f5,axiom,(
% 1.53/0.96    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.53/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.53/0.96  
% 1.53/0.96  fof(f46,plain,(
% 1.53/0.96    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.53/0.96    inference(cnf_transformation,[],[f5])).
% 1.53/0.96  
% 1.53/0.96  fof(f74,plain,(
% 1.53/0.96    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 1.53/0.96    inference(definition_unfolding,[],[f46,f70])).
% 1.53/0.96  
% 1.53/0.96  cnf(c_2,negated_conjecture,
% 1.53/0.96      ( k3_subset_1(X0,sK2) = X0 ),
% 1.53/0.96      inference(cnf_transformation,[],[f73]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1,negated_conjecture,
% 1.53/0.96      ( r1_tarski(sK2,X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f72]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_7,plain,
% 1.53/0.96      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f51]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_261,plain,
% 1.53/0.96      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK2 != X1 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_262,plain,
% 1.53/0.96      ( ~ r2_hidden(X0,sK2) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_261]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_15,negated_conjecture,
% 1.53/0.96      ( ~ v3_pre_topc(X0,sK0)
% 1.53/0.96      | ~ v4_pre_topc(X0,sK0)
% 1.53/0.96      | r2_hidden(X0,sK2)
% 1.53/0.96      | ~ r2_hidden(sK1,X0)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/0.96      inference(cnf_transformation,[],[f67]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_272,plain,
% 1.53/0.96      ( ~ v3_pre_topc(X0,sK0)
% 1.53/0.96      | ~ v4_pre_topc(X0,sK0)
% 1.53/0.96      | ~ r2_hidden(sK1,X0)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/0.96      inference(backward_subsumption_resolution,[status(thm)],[c_262,c_15]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_14,plain,
% 1.53/0.96      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.53/0.96      | ~ v4_pre_topc(X1,X0)
% 1.53/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.53/0.96      | ~ l1_pre_topc(X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f57]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_21,negated_conjecture,
% 1.53/0.96      ( l1_pre_topc(sK0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f61]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_363,plain,
% 1.53/0.96      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.53/0.96      | ~ v4_pre_topc(X1,X0)
% 1.53/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.53/0.96      | sK0 != X0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_364,plain,
% 1.53/0.96      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 1.53/0.96      | ~ v4_pre_topc(X0,sK0)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_363]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_403,plain,
% 1.53/0.96      ( ~ v4_pre_topc(X0,sK0)
% 1.53/0.96      | ~ v4_pre_topc(X1,sK0)
% 1.53/0.96      | ~ r2_hidden(sK1,X0)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.96      | k3_subset_1(u1_struct_0(sK0),X1) != X0
% 1.53/0.96      | sK0 != sK0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_272,c_364]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_404,plain,
% 1.53/0.96      ( ~ v4_pre_topc(X0,sK0)
% 1.53/0.96      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 1.53/0.96      | ~ r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0))
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.96      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_403]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_698,plain,
% 1.53/0.96      ( v4_pre_topc(X0,sK0) != iProver_top
% 1.53/0.96      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
% 1.53/0.96      | r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top
% 1.53/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.53/0.96      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1134,plain,
% 1.53/0.96      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) != iProver_top
% 1.53/0.96      | v4_pre_topc(sK2,sK0) != iProver_top
% 1.53/0.96      | r2_hidden(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) != iProver_top
% 1.53/0.96      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.53/0.96      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/0.96      inference(superposition,[status(thm)],[c_2,c_698]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1135,plain,
% 1.53/0.96      ( v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
% 1.53/0.96      | v4_pre_topc(sK2,sK0) != iProver_top
% 1.53/0.96      | r2_hidden(sK1,u1_struct_0(sK0)) != iProver_top
% 1.53/0.96      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.53/0.96      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/0.96      inference(demodulation,[status(thm)],[c_1134,c_2]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_22,negated_conjecture,
% 1.53/0.96      ( v2_pre_topc(sK0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f60]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_25,plain,
% 1.53/0.96      ( v2_pre_topc(sK0) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_26,plain,
% 1.53/0.96      ( l1_pre_topc(sK0) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_0,negated_conjecture,
% 1.53/0.96      ( v1_xboole_0(sK2) ),
% 1.53/0.96      inference(cnf_transformation,[],[f71]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_8,plain,
% 1.53/0.96      ( v4_pre_topc(X0,X1)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.96      | ~ v2_pre_topc(X1)
% 1.53/0.96      | ~ l1_pre_topc(X1)
% 1.53/0.96      | ~ v1_xboole_0(X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f52]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_303,plain,
% 1.53/0.96      ( v4_pre_topc(X0,X1)
% 1.53/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.96      | ~ v2_pre_topc(X1)
% 1.53/0.96      | ~ l1_pre_topc(X1)
% 1.53/0.96      | sK2 != X0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_304,plain,
% 1.53/0.96      ( v4_pre_topc(sK2,X0)
% 1.53/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.53/0.96      | ~ v2_pre_topc(X0)
% 1.53/0.96      | ~ l1_pre_topc(X0) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_303]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_4,negated_conjecture,
% 1.53/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 1.53/0.96      inference(cnf_transformation,[],[f75]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_316,plain,
% 1.53/0.96      ( v4_pre_topc(sK2,X0) | ~ v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 1.53/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_304,c_4]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_320,plain,
% 1.53/0.96      ( v4_pre_topc(sK2,X0) = iProver_top
% 1.53/0.96      | v2_pre_topc(X0) != iProver_top
% 1.53/0.96      | l1_pre_topc(X0) != iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_322,plain,
% 1.53/0.96      ( v4_pre_topc(sK2,sK0) = iProver_top
% 1.53/0.96      | v2_pre_topc(sK0) != iProver_top
% 1.53/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_320]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_11,plain,
% 1.53/0.96      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.53/0.96      inference(cnf_transformation,[],[f55]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_23,negated_conjecture,
% 1.53/0.96      ( ~ v2_struct_0(sK0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f59]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_276,plain,
% 1.53/0.96      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_277,plain,
% 1.53/0.96      ( ~ l1_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_276]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_65,plain,
% 1.53/0.96      ( v2_struct_0(sK0)
% 1.53/0.96      | ~ l1_struct_0(sK0)
% 1.53/0.96      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_10,plain,
% 1.53/0.96      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f54]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_68,plain,
% 1.53/0.96      ( l1_struct_0(sK0) | ~ l1_pre_topc(sK0) ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_10]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_279,plain,
% 1.53/0.96      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.53/0.96      inference(global_propositional_subsumption,
% 1.53/0.96                [status(thm)],
% 1.53/0.96                [c_277,c_23,c_21,c_65,c_68]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_323,plain,
% 1.53/0.96      ( u1_struct_0(sK0) != sK2 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_279]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_12,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.53/0.96      | ~ v2_pre_topc(X0)
% 1.53/0.96      | ~ l1_pre_topc(X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f56]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_343,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_344,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(sK0),sK0) | ~ l1_pre_topc(sK0) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_343]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_62,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(sK0),sK0)
% 1.53/0.96      | ~ v2_pre_topc(sK0)
% 1.53/0.96      | ~ l1_pre_topc(sK0) ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_12]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_346,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(sK0),sK0) ),
% 1.53/0.96      inference(global_propositional_subsumption,
% 1.53/0.96                [status(thm)],
% 1.53/0.96                [c_344,c_22,c_21,c_62]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_699,plain,
% 1.53/0.96      ( v4_pre_topc(k2_struct_0(sK0),sK0) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_9,plain,
% 1.53/0.96      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.53/0.96      inference(cnf_transformation,[],[f53]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_289,plain,
% 1.53/0.96      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.53/0.96      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_358,plain,
% 1.53/0.96      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 1.53/0.96      inference(resolution_lifted,[status(thm)],[c_289,c_21]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_359,plain,
% 1.53/0.96      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.53/0.96      inference(unflattening,[status(thm)],[c_358]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_716,plain,
% 1.53/0.96      ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
% 1.53/0.96      inference(light_normalisation,[status(thm)],[c_699,c_359]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_937,plain,
% 1.53/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_940,plain,
% 1.53/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_20,negated_conjecture,
% 1.53/0.96      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.53/0.96      inference(cnf_transformation,[],[f62]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_702,plain,
% 1.53/0.96      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_5,negated_conjecture,
% 1.53/0.96      ( r2_hidden(X0,X1)
% 1.53/0.96      | r2_hidden(X0,k3_subset_1(X2,X1))
% 1.53/0.96      | ~ m1_subset_1(X0,X2)
% 1.53/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.53/0.96      | sK2 = X2 ),
% 1.53/0.96      inference(cnf_transformation,[],[f76]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_705,plain,
% 1.53/0.96      ( sK2 = X0
% 1.53/0.96      | r2_hidden(X1,X2) = iProver_top
% 1.53/0.96      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
% 1.53/0.96      | m1_subset_1(X1,X0) != iProver_top
% 1.53/0.96      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_996,plain,
% 1.53/0.96      ( sK2 = X0
% 1.53/0.96      | r2_hidden(X1,X0) = iProver_top
% 1.53/0.96      | r2_hidden(X1,sK2) = iProver_top
% 1.53/0.96      | m1_subset_1(X1,X0) != iProver_top
% 1.53/0.96      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.53/0.96      inference(superposition,[status(thm)],[c_2,c_705]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_44,plain,
% 1.53/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1001,plain,
% 1.53/0.96      ( m1_subset_1(X1,X0) != iProver_top
% 1.53/0.96      | r2_hidden(X1,sK2) = iProver_top
% 1.53/0.96      | r2_hidden(X1,X0) = iProver_top
% 1.53/0.96      | sK2 = X0 ),
% 1.53/0.96      inference(global_propositional_subsumption,[status(thm)],[c_996,c_44]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1002,plain,
% 1.53/0.96      ( sK2 = X0
% 1.53/0.96      | r2_hidden(X1,X0) = iProver_top
% 1.53/0.96      | r2_hidden(X1,sK2) = iProver_top
% 1.53/0.96      | m1_subset_1(X1,X0) != iProver_top ),
% 1.53/0.96      inference(renaming,[status(thm)],[c_1001]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1012,plain,
% 1.53/0.96      ( u1_struct_0(sK0) = sK2
% 1.53/0.96      | r2_hidden(sK1,u1_struct_0(sK0)) = iProver_top
% 1.53/0.96      | r2_hidden(sK1,sK2) = iProver_top ),
% 1.53/0.96      inference(superposition,[status(thm)],[c_702,c_1002]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1215,plain,
% 1.53/0.96      ( ~ r2_hidden(sK1,sK2) ),
% 1.53/0.96      inference(instantiation,[status(thm)],[c_262]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1216,plain,
% 1.53/0.96      ( r2_hidden(sK1,sK2) != iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1233,plain,
% 1.53/0.96      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/0.96      inference(global_propositional_subsumption,
% 1.53/0.96                [status(thm)],
% 1.53/0.96                [c_1135,c_25,c_26,c_322,c_323,c_716,c_940,c_1012,c_1216]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_3,negated_conjecture,
% 1.53/0.96      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
% 1.53/0.96      inference(cnf_transformation,[],[f74]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_707,plain,
% 1.53/0.96      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) = iProver_top ),
% 1.53/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_725,plain,
% 1.53/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.53/0.96      inference(light_normalisation,[status(thm)],[c_707,c_2]) ).
% 1.53/0.96  
% 1.53/0.96  cnf(c_1238,plain,
% 1.53/0.96      ( $false ),
% 1.53/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_1233,c_725]) ).
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.53/0.96  
% 1.53/0.96  ------                               Statistics
% 1.53/0.96  
% 1.53/0.96  ------ General
% 1.53/0.96  
% 1.53/0.96  abstr_ref_over_cycles:                  0
% 1.53/0.96  abstr_ref_under_cycles:                 0
% 1.53/0.96  gc_basic_clause_elim:                   0
% 1.53/0.96  forced_gc_time:                         0
% 1.53/0.96  parsing_time:                           0.009
% 1.53/0.96  unif_index_cands_time:                  0.
% 1.53/0.96  unif_index_add_time:                    0.
% 1.53/0.96  orderings_time:                         0.
% 1.53/0.96  out_proof_time:                         0.012
% 1.53/0.96  total_time:                             0.073
% 1.53/0.96  num_of_symbols:                         48
% 1.53/0.96  num_of_terms:                           1168
% 1.53/0.96  
% 1.53/0.96  ------ Preprocessing
% 1.53/0.96  
% 1.53/0.96  num_of_splits:                          0
% 1.53/0.96  num_of_split_atoms:                     0
% 1.53/0.96  num_of_reused_defs:                     0
% 1.53/0.96  num_eq_ax_congr_red:                    3
% 1.53/0.96  num_of_sem_filtered_clauses:            1
% 1.53/0.96  num_of_subtypes:                        0
% 1.53/0.96  monotx_restored_types:                  0
% 1.53/0.96  sat_num_of_epr_types:                   0
% 1.53/0.96  sat_num_of_non_cyclic_types:            0
% 1.53/0.96  sat_guarded_non_collapsed_types:        0
% 1.53/0.96  num_pure_diseq_elim:                    0
% 1.53/0.96  simp_replaced_by:                       0
% 1.53/0.96  res_preprocessed:                       82
% 1.53/0.96  prep_upred:                             0
% 1.53/0.96  prep_unflattend:                        10
% 1.53/0.96  smt_new_axioms:                         0
% 1.53/0.96  pred_elim_cands:                        3
% 1.53/0.96  pred_elim:                              7
% 1.53/0.96  pred_elim_cl:                           11
% 1.53/0.96  pred_elim_cycles:                       9
% 1.53/0.96  merged_defs:                            0
% 1.53/0.96  merged_defs_ncl:                        0
% 1.53/0.96  bin_hyper_res:                          0
% 1.53/0.96  prep_cycles:                            4
% 1.53/0.96  pred_elim_time:                         0.003
% 1.53/0.96  splitting_time:                         0.
% 1.53/0.96  sem_filter_time:                        0.
% 1.53/0.96  monotx_time:                            0.
% 1.53/0.96  subtype_inf_time:                       0.
% 1.53/0.96  
% 1.53/0.96  ------ Problem properties
% 1.53/0.96  
% 1.53/0.96  clauses:                                13
% 1.53/0.96  conjectures:                            6
% 1.53/0.96  epr:                                    2
% 1.53/0.96  horn:                                   12
% 1.53/0.96  ground:                                 6
% 1.53/0.96  unary:                                  10
% 1.53/0.96  binary:                                 0
% 1.53/0.96  lits:                                   23
% 1.53/0.96  lits_eq:                                4
% 1.53/0.96  fd_pure:                                0
% 1.53/0.96  fd_pseudo:                              0
% 1.53/0.96  fd_cond:                                1
% 1.53/0.96  fd_pseudo_cond:                         0
% 1.53/0.96  ac_symbols:                             0
% 1.53/0.96  
% 1.53/0.96  ------ Propositional Solver
% 1.53/0.96  
% 1.53/0.96  prop_solver_calls:                      25
% 1.53/0.96  prop_fast_solver_calls:                 417
% 1.53/0.96  smt_solver_calls:                       0
% 1.53/0.96  smt_fast_solver_calls:                  0
% 1.53/0.96  prop_num_of_clauses:                    418
% 1.53/0.96  prop_preprocess_simplified:             2172
% 1.53/0.96  prop_fo_subsumed:                       8
% 1.53/0.96  prop_solver_time:                       0.
% 1.53/0.96  smt_solver_time:                        0.
% 1.53/0.96  smt_fast_solver_time:                   0.
% 1.53/0.96  prop_fast_solver_time:                  0.
% 1.53/0.96  prop_unsat_core_time:                   0.
% 1.53/0.96  
% 1.53/0.96  ------ QBF
% 1.53/0.96  
% 1.53/0.96  qbf_q_res:                              0
% 1.53/0.96  qbf_num_tautologies:                    0
% 1.53/0.96  qbf_prep_cycles:                        0
% 1.53/0.96  
% 1.53/0.96  ------ BMC1
% 1.53/0.96  
% 1.53/0.96  bmc1_current_bound:                     -1
% 1.53/0.96  bmc1_last_solved_bound:                 -1
% 1.53/0.96  bmc1_unsat_core_size:                   -1
% 1.53/0.96  bmc1_unsat_core_parents_size:           -1
% 1.53/0.96  bmc1_merge_next_fun:                    0
% 1.53/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.53/0.96  
% 1.53/0.96  ------ Instantiation
% 1.53/0.96  
% 1.53/0.96  inst_num_of_clauses:                    112
% 1.53/0.96  inst_num_in_passive:                    44
% 1.53/0.96  inst_num_in_active:                     56
% 1.53/0.96  inst_num_in_unprocessed:                13
% 1.53/0.96  inst_num_of_loops:                      60
% 1.53/0.96  inst_num_of_learning_restarts:          0
% 1.53/0.96  inst_num_moves_active_passive:          2
% 1.53/0.96  inst_lit_activity:                      0
% 1.53/0.96  inst_lit_activity_moves:                0
% 1.53/0.96  inst_num_tautologies:                   0
% 1.53/0.96  inst_num_prop_implied:                  0
% 1.53/0.96  inst_num_existing_simplified:           0
% 1.53/0.96  inst_num_eq_res_simplified:             0
% 1.53/0.96  inst_num_child_elim:                    0
% 1.53/0.96  inst_num_of_dismatching_blockings:      12
% 1.53/0.96  inst_num_of_non_proper_insts:           74
% 1.53/0.96  inst_num_of_duplicates:                 0
% 1.53/0.96  inst_inst_num_from_inst_to_res:         0
% 1.53/0.96  inst_dismatching_checking_time:         0.
% 1.53/0.96  
% 1.53/0.96  ------ Resolution
% 1.53/0.96  
% 1.53/0.96  res_num_of_clauses:                     0
% 1.53/0.96  res_num_in_passive:                     0
% 1.53/0.96  res_num_in_active:                      0
% 1.53/0.96  res_num_of_loops:                       86
% 1.53/0.96  res_forward_subset_subsumed:            7
% 1.53/0.96  res_backward_subset_subsumed:           3
% 1.53/0.96  res_forward_subsumed:                   0
% 1.53/0.96  res_backward_subsumed:                  2
% 1.53/0.96  res_forward_subsumption_resolution:     1
% 1.53/0.96  res_backward_subsumption_resolution:    1
% 1.53/0.96  res_clause_to_clause_subsumption:       40
% 1.53/0.96  res_orphan_elimination:                 0
% 1.53/0.96  res_tautology_del:                      7
% 1.53/0.96  res_num_eq_res_simplified:              0
% 1.53/0.96  res_num_sel_changes:                    0
% 1.53/0.96  res_moves_from_active_to_pass:          0
% 1.53/0.96  
% 1.53/0.96  ------ Superposition
% 1.53/0.96  
% 1.53/0.96  sup_time_total:                         0.
% 1.53/0.96  sup_time_generating:                    0.
% 1.53/0.96  sup_time_sim_full:                      0.
% 1.53/0.96  sup_time_sim_immed:                     0.
% 1.53/0.96  
% 1.53/0.96  sup_num_of_clauses:                     17
% 1.53/0.96  sup_num_in_active:                      10
% 1.53/0.96  sup_num_in_passive:                     7
% 1.53/0.96  sup_num_of_loops:                       10
% 1.53/0.96  sup_fw_superposition:                   7
% 1.53/0.96  sup_bw_superposition:                   0
% 1.53/0.96  sup_immediate_simplified:               2
% 1.53/0.96  sup_given_eliminated:                   0
% 1.53/0.96  comparisons_done:                       0
% 1.53/0.96  comparisons_avoided:                    0
% 1.53/0.96  
% 1.53/0.96  ------ Simplifications
% 1.53/0.96  
% 1.53/0.96  
% 1.53/0.96  sim_fw_subset_subsumed:                 1
% 1.53/0.96  sim_bw_subset_subsumed:                 0
% 1.53/0.96  sim_fw_subsumed:                        1
% 1.53/0.96  sim_bw_subsumed:                        0
% 1.53/0.96  sim_fw_subsumption_res:                 1
% 1.53/0.96  sim_bw_subsumption_res:                 0
% 1.53/0.96  sim_tautology_del:                      0
% 1.53/0.96  sim_eq_tautology_del:                   0
% 1.53/0.96  sim_eq_res_simp:                        0
% 1.53/0.96  sim_fw_demodulated:                     1
% 1.53/0.96  sim_bw_demodulated:                     0
% 1.53/0.96  sim_light_normalised:                   2
% 1.53/0.96  sim_joinable_taut:                      0
% 1.53/0.96  sim_joinable_simp:                      0
% 1.53/0.96  sim_ac_normalised:                      0
% 1.53/0.96  sim_smt_subsumption:                    0
% 1.53/0.96  
%------------------------------------------------------------------------------
