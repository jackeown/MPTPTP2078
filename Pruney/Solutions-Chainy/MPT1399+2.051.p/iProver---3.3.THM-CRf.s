%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:41 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 483 expanded)
%              Number of clauses        :   64 (  89 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   25
%              Number of atoms          :  461 (4892 expanded)
%              Number of equality atoms :  103 ( 486 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f45,plain,(
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
     => ( k1_xboole_0 = sK3
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
                    | ~ r2_hidden(sK2,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK2,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
                      | ~ v4_pre_topc(X3,sK1)
                      | ~ v3_pre_topc(X3,sK1) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK1)
                        & v3_pre_topc(X3,sK1) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 = sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | ~ r2_hidden(sK2,X3)
            | ~ v4_pre_topc(X3,sK1)
            | ~ v3_pre_topc(X3,sK1) )
          & ( ( r2_hidden(sK2,X3)
              & v4_pre_topc(X3,sK1)
              & v3_pre_topc(X3,sK1) )
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).

fof(f72,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f78,plain,(
    k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ! [X0] : k1_subset_1(X0) = sK3 ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f80,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK3) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f83,plain,(
    ! [X0] : k3_subset_1(X0,sK3) = X0 ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK3 = X0 ) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0] : r1_tarski(sK3,X0) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(sK2,X3)
      | ~ v4_pre_topc(X3,sK1)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    k6_relat_1(sK3) = sK3 ),
    inference(definition_unfolding,[],[f58,f78,f78])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = sK3 ),
    inference(definition_unfolding,[],[f57,f78,f78])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,(
    v1_xboole_0(sK3) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_768,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_316,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_12])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_448,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_26])).

cnf(c_449,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_788,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_768,c_449])).

cnf(c_2,negated_conjecture,
    ( k3_subset_1(X0,sK3) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK3 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_772,plain,
    ( sK3 = X0
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1080,plain,
    ( sK3 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_772])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1316,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1080,c_50])).

cnf(c_1317,plain,
    ( sK3 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1316])).

cnf(c_1480,plain,
    ( k2_struct_0(sK1) = sK3
    | r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_1317])).

cnf(c_15,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_433,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_434,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_436,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_26])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1,negated_conjecture,
    ( r1_tarski(sK3,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_302,plain,
    ( ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_312,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_302,c_20])).

cnf(c_352,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_312])).

cnf(c_353,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_355,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_27,c_26])).

cnf(c_445,plain,
    ( ~ r2_hidden(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_436,c_355])).

cnf(c_764,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_810,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_764,c_449])).

cnf(c_3,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_775,plain,
    ( m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_775,c_2])).

cnf(c_813,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_810,c_799])).

cnf(c_2294,plain,
    ( k2_struct_0(sK1) = sK3
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_813])).

cnf(c_767,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_2300,plain,
    ( k2_struct_0(sK1) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2294,c_767])).

cnf(c_19,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_402,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_403,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_405,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_27,c_26])).

cnf(c_766,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_795,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_766,c_449])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_770,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1657,plain,
    ( k9_relat_1(k6_relat_1(k2_struct_0(sK1)),sK0(sK1)) = sK0(sK1) ),
    inference(superposition,[status(thm)],[c_795,c_770])).

cnf(c_2303,plain,
    ( k9_relat_1(k6_relat_1(sK3),sK0(sK1)) = sK0(sK1) ),
    inference(demodulation,[status(thm)],[c_2300,c_1657])).

cnf(c_9,negated_conjecture,
    ( k6_relat_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2316,plain,
    ( k9_relat_1(sK3,sK0(sK1)) = sK0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2303,c_9])).

cnf(c_8,negated_conjecture,
    ( k9_relat_1(sK3,X0) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2317,plain,
    ( sK0(sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_2316,c_8])).

cnf(c_0,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_330,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_394,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(X0) != sK3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_330,c_28])).

cnf(c_395,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1) != sK3 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2317,c_395,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.20/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/0.98  
% 2.20/0.98  ------  iProver source info
% 2.20/0.98  
% 2.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/0.98  git: non_committed_changes: false
% 2.20/0.98  git: last_make_outside_of_git: false
% 2.20/0.98  
% 2.20/0.98  ------ 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options
% 2.20/0.98  
% 2.20/0.98  --out_options                           all
% 2.20/0.98  --tptp_safe_out                         true
% 2.20/0.98  --problem_path                          ""
% 2.20/0.98  --include_path                          ""
% 2.20/0.98  --clausifier                            res/vclausify_rel
% 2.20/0.98  --clausifier_options                    --mode clausify
% 2.20/0.98  --stdin                                 false
% 2.20/0.98  --stats_out                             all
% 2.20/0.98  
% 2.20/0.98  ------ General Options
% 2.20/0.98  
% 2.20/0.98  --fof                                   false
% 2.20/0.98  --time_out_real                         305.
% 2.20/0.98  --time_out_virtual                      -1.
% 2.20/0.98  --symbol_type_check                     false
% 2.20/0.98  --clausify_out                          false
% 2.20/0.98  --sig_cnt_out                           false
% 2.20/0.98  --trig_cnt_out                          false
% 2.20/0.98  --trig_cnt_out_tolerance                1.
% 2.20/0.98  --trig_cnt_out_sk_spl                   false
% 2.20/0.98  --abstr_cl_out                          false
% 2.20/0.98  
% 2.20/0.98  ------ Global Options
% 2.20/0.98  
% 2.20/0.98  --schedule                              default
% 2.20/0.98  --add_important_lit                     false
% 2.20/0.98  --prop_solver_per_cl                    1000
% 2.20/0.98  --min_unsat_core                        false
% 2.20/0.98  --soft_assumptions                      false
% 2.20/0.98  --soft_lemma_size                       3
% 2.20/0.98  --prop_impl_unit_size                   0
% 2.20/0.98  --prop_impl_unit                        []
% 2.20/0.98  --share_sel_clauses                     true
% 2.20/0.98  --reset_solvers                         false
% 2.20/0.98  --bc_imp_inh                            [conj_cone]
% 2.20/0.98  --conj_cone_tolerance                   3.
% 2.20/0.98  --extra_neg_conj                        none
% 2.20/0.98  --large_theory_mode                     true
% 2.20/0.98  --prolific_symb_bound                   200
% 2.20/0.98  --lt_threshold                          2000
% 2.20/0.98  --clause_weak_htbl                      true
% 2.20/0.98  --gc_record_bc_elim                     false
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing Options
% 2.20/0.98  
% 2.20/0.98  --preprocessing_flag                    true
% 2.20/0.98  --time_out_prep_mult                    0.1
% 2.20/0.98  --splitting_mode                        input
% 2.20/0.98  --splitting_grd                         true
% 2.20/0.98  --splitting_cvd                         false
% 2.20/0.98  --splitting_cvd_svl                     false
% 2.20/0.98  --splitting_nvd                         32
% 2.20/0.98  --sub_typing                            true
% 2.20/0.98  --prep_gs_sim                           true
% 2.20/0.98  --prep_unflatten                        true
% 2.20/0.98  --prep_res_sim                          true
% 2.20/0.98  --prep_upred                            true
% 2.20/0.98  --prep_sem_filter                       exhaustive
% 2.20/0.98  --prep_sem_filter_out                   false
% 2.20/0.98  --pred_elim                             true
% 2.20/0.98  --res_sim_input                         true
% 2.20/0.98  --eq_ax_congr_red                       true
% 2.20/0.98  --pure_diseq_elim                       true
% 2.20/0.98  --brand_transform                       false
% 2.20/0.98  --non_eq_to_eq                          false
% 2.20/0.98  --prep_def_merge                        true
% 2.20/0.98  --prep_def_merge_prop_impl              false
% 2.20/0.98  --prep_def_merge_mbd                    true
% 2.20/0.98  --prep_def_merge_tr_red                 false
% 2.20/0.98  --prep_def_merge_tr_cl                  false
% 2.20/0.98  --smt_preprocessing                     true
% 2.20/0.98  --smt_ac_axioms                         fast
% 2.20/0.98  --preprocessed_out                      false
% 2.20/0.98  --preprocessed_stats                    false
% 2.20/0.98  
% 2.20/0.98  ------ Abstraction refinement Options
% 2.20/0.98  
% 2.20/0.98  --abstr_ref                             []
% 2.20/0.98  --abstr_ref_prep                        false
% 2.20/0.98  --abstr_ref_until_sat                   false
% 2.20/0.98  --abstr_ref_sig_restrict                funpre
% 2.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/0.98  --abstr_ref_under                       []
% 2.20/0.98  
% 2.20/0.98  ------ SAT Options
% 2.20/0.98  
% 2.20/0.98  --sat_mode                              false
% 2.20/0.98  --sat_fm_restart_options                ""
% 2.20/0.98  --sat_gr_def                            false
% 2.20/0.98  --sat_epr_types                         true
% 2.20/0.98  --sat_non_cyclic_types                  false
% 2.20/0.98  --sat_finite_models                     false
% 2.20/0.98  --sat_fm_lemmas                         false
% 2.20/0.98  --sat_fm_prep                           false
% 2.20/0.98  --sat_fm_uc_incr                        true
% 2.20/0.98  --sat_out_model                         small
% 2.20/0.98  --sat_out_clauses                       false
% 2.20/0.98  
% 2.20/0.98  ------ QBF Options
% 2.20/0.98  
% 2.20/0.98  --qbf_mode                              false
% 2.20/0.98  --qbf_elim_univ                         false
% 2.20/0.98  --qbf_dom_inst                          none
% 2.20/0.98  --qbf_dom_pre_inst                      false
% 2.20/0.98  --qbf_sk_in                             false
% 2.20/0.98  --qbf_pred_elim                         true
% 2.20/0.98  --qbf_split                             512
% 2.20/0.98  
% 2.20/0.98  ------ BMC1 Options
% 2.20/0.98  
% 2.20/0.98  --bmc1_incremental                      false
% 2.20/0.98  --bmc1_axioms                           reachable_all
% 2.20/0.98  --bmc1_min_bound                        0
% 2.20/0.98  --bmc1_max_bound                        -1
% 2.20/0.98  --bmc1_max_bound_default                -1
% 2.20/0.98  --bmc1_symbol_reachability              true
% 2.20/0.98  --bmc1_property_lemmas                  false
% 2.20/0.98  --bmc1_k_induction                      false
% 2.20/0.98  --bmc1_non_equiv_states                 false
% 2.20/0.98  --bmc1_deadlock                         false
% 2.20/0.98  --bmc1_ucm                              false
% 2.20/0.98  --bmc1_add_unsat_core                   none
% 2.20/0.98  --bmc1_unsat_core_children              false
% 2.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/0.98  --bmc1_out_stat                         full
% 2.20/0.98  --bmc1_ground_init                      false
% 2.20/0.98  --bmc1_pre_inst_next_state              false
% 2.20/0.98  --bmc1_pre_inst_state                   false
% 2.20/0.98  --bmc1_pre_inst_reach_state             false
% 2.20/0.98  --bmc1_out_unsat_core                   false
% 2.20/0.98  --bmc1_aig_witness_out                  false
% 2.20/0.98  --bmc1_verbose                          false
% 2.20/0.98  --bmc1_dump_clauses_tptp                false
% 2.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.20/0.98  --bmc1_dump_file                        -
% 2.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.20/0.98  --bmc1_ucm_extend_mode                  1
% 2.20/0.98  --bmc1_ucm_init_mode                    2
% 2.20/0.98  --bmc1_ucm_cone_mode                    none
% 2.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.20/0.98  --bmc1_ucm_relax_model                  4
% 2.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/0.98  --bmc1_ucm_layered_model                none
% 2.20/0.98  --bmc1_ucm_max_lemma_size               10
% 2.20/0.98  
% 2.20/0.98  ------ AIG Options
% 2.20/0.98  
% 2.20/0.98  --aig_mode                              false
% 2.20/0.98  
% 2.20/0.98  ------ Instantiation Options
% 2.20/0.98  
% 2.20/0.98  --instantiation_flag                    true
% 2.20/0.98  --inst_sos_flag                         false
% 2.20/0.98  --inst_sos_phase                        true
% 2.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel_side                     num_symb
% 2.20/0.98  --inst_solver_per_active                1400
% 2.20/0.98  --inst_solver_calls_frac                1.
% 2.20/0.98  --inst_passive_queue_type               priority_queues
% 2.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/0.98  --inst_passive_queues_freq              [25;2]
% 2.20/0.98  --inst_dismatching                      true
% 2.20/0.98  --inst_eager_unprocessed_to_passive     true
% 2.20/0.98  --inst_prop_sim_given                   true
% 2.20/0.98  --inst_prop_sim_new                     false
% 2.20/0.98  --inst_subs_new                         false
% 2.20/0.98  --inst_eq_res_simp                      false
% 2.20/0.98  --inst_subs_given                       false
% 2.20/0.98  --inst_orphan_elimination               true
% 2.20/0.98  --inst_learning_loop_flag               true
% 2.20/0.98  --inst_learning_start                   3000
% 2.20/0.98  --inst_learning_factor                  2
% 2.20/0.98  --inst_start_prop_sim_after_learn       3
% 2.20/0.98  --inst_sel_renew                        solver
% 2.20/0.98  --inst_lit_activity_flag                true
% 2.20/0.98  --inst_restr_to_given                   false
% 2.20/0.98  --inst_activity_threshold               500
% 2.20/0.98  --inst_out_proof                        true
% 2.20/0.98  
% 2.20/0.98  ------ Resolution Options
% 2.20/0.98  
% 2.20/0.98  --resolution_flag                       true
% 2.20/0.98  --res_lit_sel                           adaptive
% 2.20/0.98  --res_lit_sel_side                      none
% 2.20/0.98  --res_ordering                          kbo
% 2.20/0.98  --res_to_prop_solver                    active
% 2.20/0.98  --res_prop_simpl_new                    false
% 2.20/0.98  --res_prop_simpl_given                  true
% 2.20/0.98  --res_passive_queue_type                priority_queues
% 2.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/0.98  --res_passive_queues_freq               [15;5]
% 2.20/0.98  --res_forward_subs                      full
% 2.20/0.98  --res_backward_subs                     full
% 2.20/0.98  --res_forward_subs_resolution           true
% 2.20/0.98  --res_backward_subs_resolution          true
% 2.20/0.98  --res_orphan_elimination                true
% 2.20/0.98  --res_time_limit                        2.
% 2.20/0.98  --res_out_proof                         true
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Options
% 2.20/0.98  
% 2.20/0.98  --superposition_flag                    true
% 2.20/0.98  --sup_passive_queue_type                priority_queues
% 2.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.20/0.98  --demod_completeness_check              fast
% 2.20/0.98  --demod_use_ground                      true
% 2.20/0.98  --sup_to_prop_solver                    passive
% 2.20/0.98  --sup_prop_simpl_new                    true
% 2.20/0.98  --sup_prop_simpl_given                  true
% 2.20/0.98  --sup_fun_splitting                     false
% 2.20/0.98  --sup_smt_interval                      50000
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Simplification Setup
% 2.20/0.98  
% 2.20/0.98  --sup_indices_passive                   []
% 2.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_full_bw                           [BwDemod]
% 2.20/0.98  --sup_immed_triv                        [TrivRules]
% 2.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_immed_bw_main                     []
% 2.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  
% 2.20/0.98  ------ Combination Options
% 2.20/0.98  
% 2.20/0.98  --comb_res_mult                         3
% 2.20/0.98  --comb_sup_mult                         2
% 2.20/0.98  --comb_inst_mult                        10
% 2.20/0.98  
% 2.20/0.98  ------ Debug Options
% 2.20/0.98  
% 2.20/0.98  --dbg_backtrace                         false
% 2.20/0.98  --dbg_dump_prop_clauses                 false
% 2.20/0.98  --dbg_dump_prop_clauses_file            -
% 2.20/0.98  --dbg_out_stat                          false
% 2.20/0.98  ------ Parsing...
% 2.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.20/0.98  ------ Proving...
% 2.20/0.98  ------ Problem Properties 
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  clauses                                 17
% 2.20/0.98  conjectures                             8
% 2.20/0.98  EPR                                     1
% 2.20/0.98  Horn                                    16
% 2.20/0.98  unary                                   12
% 2.20/0.98  binary                                  3
% 2.20/0.98  lits                                    26
% 2.20/0.98  lits eq                                 8
% 2.20/0.98  fd_pure                                 0
% 2.20/0.98  fd_pseudo                               0
% 2.20/0.98  fd_cond                                 1
% 2.20/0.98  fd_pseudo_cond                          0
% 2.20/0.98  AC symbols                              0
% 2.20/0.98  
% 2.20/0.98  ------ Schedule dynamic 5 is on 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  ------ 
% 2.20/0.98  Current options:
% 2.20/0.98  ------ 
% 2.20/0.98  
% 2.20/0.98  ------ Input Options
% 2.20/0.98  
% 2.20/0.98  --out_options                           all
% 2.20/0.98  --tptp_safe_out                         true
% 2.20/0.98  --problem_path                          ""
% 2.20/0.98  --include_path                          ""
% 2.20/0.98  --clausifier                            res/vclausify_rel
% 2.20/0.98  --clausifier_options                    --mode clausify
% 2.20/0.98  --stdin                                 false
% 2.20/0.98  --stats_out                             all
% 2.20/0.98  
% 2.20/0.98  ------ General Options
% 2.20/0.98  
% 2.20/0.98  --fof                                   false
% 2.20/0.98  --time_out_real                         305.
% 2.20/0.98  --time_out_virtual                      -1.
% 2.20/0.98  --symbol_type_check                     false
% 2.20/0.98  --clausify_out                          false
% 2.20/0.98  --sig_cnt_out                           false
% 2.20/0.98  --trig_cnt_out                          false
% 2.20/0.98  --trig_cnt_out_tolerance                1.
% 2.20/0.98  --trig_cnt_out_sk_spl                   false
% 2.20/0.98  --abstr_cl_out                          false
% 2.20/0.98  
% 2.20/0.98  ------ Global Options
% 2.20/0.98  
% 2.20/0.98  --schedule                              default
% 2.20/0.98  --add_important_lit                     false
% 2.20/0.98  --prop_solver_per_cl                    1000
% 2.20/0.98  --min_unsat_core                        false
% 2.20/0.98  --soft_assumptions                      false
% 2.20/0.98  --soft_lemma_size                       3
% 2.20/0.98  --prop_impl_unit_size                   0
% 2.20/0.98  --prop_impl_unit                        []
% 2.20/0.98  --share_sel_clauses                     true
% 2.20/0.98  --reset_solvers                         false
% 2.20/0.98  --bc_imp_inh                            [conj_cone]
% 2.20/0.98  --conj_cone_tolerance                   3.
% 2.20/0.98  --extra_neg_conj                        none
% 2.20/0.98  --large_theory_mode                     true
% 2.20/0.98  --prolific_symb_bound                   200
% 2.20/0.98  --lt_threshold                          2000
% 2.20/0.98  --clause_weak_htbl                      true
% 2.20/0.98  --gc_record_bc_elim                     false
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing Options
% 2.20/0.98  
% 2.20/0.98  --preprocessing_flag                    true
% 2.20/0.98  --time_out_prep_mult                    0.1
% 2.20/0.98  --splitting_mode                        input
% 2.20/0.98  --splitting_grd                         true
% 2.20/0.98  --splitting_cvd                         false
% 2.20/0.98  --splitting_cvd_svl                     false
% 2.20/0.98  --splitting_nvd                         32
% 2.20/0.98  --sub_typing                            true
% 2.20/0.98  --prep_gs_sim                           true
% 2.20/0.98  --prep_unflatten                        true
% 2.20/0.98  --prep_res_sim                          true
% 2.20/0.98  --prep_upred                            true
% 2.20/0.98  --prep_sem_filter                       exhaustive
% 2.20/0.98  --prep_sem_filter_out                   false
% 2.20/0.98  --pred_elim                             true
% 2.20/0.98  --res_sim_input                         true
% 2.20/0.98  --eq_ax_congr_red                       true
% 2.20/0.98  --pure_diseq_elim                       true
% 2.20/0.98  --brand_transform                       false
% 2.20/0.98  --non_eq_to_eq                          false
% 2.20/0.98  --prep_def_merge                        true
% 2.20/0.98  --prep_def_merge_prop_impl              false
% 2.20/0.98  --prep_def_merge_mbd                    true
% 2.20/0.98  --prep_def_merge_tr_red                 false
% 2.20/0.98  --prep_def_merge_tr_cl                  false
% 2.20/0.98  --smt_preprocessing                     true
% 2.20/0.98  --smt_ac_axioms                         fast
% 2.20/0.98  --preprocessed_out                      false
% 2.20/0.98  --preprocessed_stats                    false
% 2.20/0.98  
% 2.20/0.98  ------ Abstraction refinement Options
% 2.20/0.98  
% 2.20/0.98  --abstr_ref                             []
% 2.20/0.98  --abstr_ref_prep                        false
% 2.20/0.98  --abstr_ref_until_sat                   false
% 2.20/0.98  --abstr_ref_sig_restrict                funpre
% 2.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/0.98  --abstr_ref_under                       []
% 2.20/0.98  
% 2.20/0.98  ------ SAT Options
% 2.20/0.98  
% 2.20/0.98  --sat_mode                              false
% 2.20/0.98  --sat_fm_restart_options                ""
% 2.20/0.98  --sat_gr_def                            false
% 2.20/0.98  --sat_epr_types                         true
% 2.20/0.98  --sat_non_cyclic_types                  false
% 2.20/0.98  --sat_finite_models                     false
% 2.20/0.98  --sat_fm_lemmas                         false
% 2.20/0.98  --sat_fm_prep                           false
% 2.20/0.98  --sat_fm_uc_incr                        true
% 2.20/0.98  --sat_out_model                         small
% 2.20/0.98  --sat_out_clauses                       false
% 2.20/0.98  
% 2.20/0.98  ------ QBF Options
% 2.20/0.98  
% 2.20/0.98  --qbf_mode                              false
% 2.20/0.98  --qbf_elim_univ                         false
% 2.20/0.98  --qbf_dom_inst                          none
% 2.20/0.98  --qbf_dom_pre_inst                      false
% 2.20/0.98  --qbf_sk_in                             false
% 2.20/0.98  --qbf_pred_elim                         true
% 2.20/0.98  --qbf_split                             512
% 2.20/0.98  
% 2.20/0.98  ------ BMC1 Options
% 2.20/0.98  
% 2.20/0.98  --bmc1_incremental                      false
% 2.20/0.98  --bmc1_axioms                           reachable_all
% 2.20/0.98  --bmc1_min_bound                        0
% 2.20/0.98  --bmc1_max_bound                        -1
% 2.20/0.98  --bmc1_max_bound_default                -1
% 2.20/0.98  --bmc1_symbol_reachability              true
% 2.20/0.98  --bmc1_property_lemmas                  false
% 2.20/0.98  --bmc1_k_induction                      false
% 2.20/0.98  --bmc1_non_equiv_states                 false
% 2.20/0.98  --bmc1_deadlock                         false
% 2.20/0.98  --bmc1_ucm                              false
% 2.20/0.98  --bmc1_add_unsat_core                   none
% 2.20/0.98  --bmc1_unsat_core_children              false
% 2.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/0.98  --bmc1_out_stat                         full
% 2.20/0.98  --bmc1_ground_init                      false
% 2.20/0.98  --bmc1_pre_inst_next_state              false
% 2.20/0.98  --bmc1_pre_inst_state                   false
% 2.20/0.98  --bmc1_pre_inst_reach_state             false
% 2.20/0.98  --bmc1_out_unsat_core                   false
% 2.20/0.98  --bmc1_aig_witness_out                  false
% 2.20/0.98  --bmc1_verbose                          false
% 2.20/0.98  --bmc1_dump_clauses_tptp                false
% 2.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.20/0.98  --bmc1_dump_file                        -
% 2.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.20/0.98  --bmc1_ucm_extend_mode                  1
% 2.20/0.98  --bmc1_ucm_init_mode                    2
% 2.20/0.98  --bmc1_ucm_cone_mode                    none
% 2.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.20/0.98  --bmc1_ucm_relax_model                  4
% 2.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/0.98  --bmc1_ucm_layered_model                none
% 2.20/0.98  --bmc1_ucm_max_lemma_size               10
% 2.20/0.98  
% 2.20/0.98  ------ AIG Options
% 2.20/0.98  
% 2.20/0.98  --aig_mode                              false
% 2.20/0.98  
% 2.20/0.98  ------ Instantiation Options
% 2.20/0.98  
% 2.20/0.98  --instantiation_flag                    true
% 2.20/0.98  --inst_sos_flag                         false
% 2.20/0.98  --inst_sos_phase                        true
% 2.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/0.98  --inst_lit_sel_side                     none
% 2.20/0.98  --inst_solver_per_active                1400
% 2.20/0.98  --inst_solver_calls_frac                1.
% 2.20/0.98  --inst_passive_queue_type               priority_queues
% 2.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/0.98  --inst_passive_queues_freq              [25;2]
% 2.20/0.98  --inst_dismatching                      true
% 2.20/0.98  --inst_eager_unprocessed_to_passive     true
% 2.20/0.98  --inst_prop_sim_given                   true
% 2.20/0.98  --inst_prop_sim_new                     false
% 2.20/0.98  --inst_subs_new                         false
% 2.20/0.98  --inst_eq_res_simp                      false
% 2.20/0.98  --inst_subs_given                       false
% 2.20/0.98  --inst_orphan_elimination               true
% 2.20/0.98  --inst_learning_loop_flag               true
% 2.20/0.98  --inst_learning_start                   3000
% 2.20/0.98  --inst_learning_factor                  2
% 2.20/0.98  --inst_start_prop_sim_after_learn       3
% 2.20/0.98  --inst_sel_renew                        solver
% 2.20/0.98  --inst_lit_activity_flag                true
% 2.20/0.98  --inst_restr_to_given                   false
% 2.20/0.98  --inst_activity_threshold               500
% 2.20/0.98  --inst_out_proof                        true
% 2.20/0.98  
% 2.20/0.98  ------ Resolution Options
% 2.20/0.98  
% 2.20/0.98  --resolution_flag                       false
% 2.20/0.98  --res_lit_sel                           adaptive
% 2.20/0.98  --res_lit_sel_side                      none
% 2.20/0.98  --res_ordering                          kbo
% 2.20/0.98  --res_to_prop_solver                    active
% 2.20/0.98  --res_prop_simpl_new                    false
% 2.20/0.98  --res_prop_simpl_given                  true
% 2.20/0.98  --res_passive_queue_type                priority_queues
% 2.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/0.98  --res_passive_queues_freq               [15;5]
% 2.20/0.98  --res_forward_subs                      full
% 2.20/0.98  --res_backward_subs                     full
% 2.20/0.98  --res_forward_subs_resolution           true
% 2.20/0.98  --res_backward_subs_resolution          true
% 2.20/0.98  --res_orphan_elimination                true
% 2.20/0.98  --res_time_limit                        2.
% 2.20/0.98  --res_out_proof                         true
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Options
% 2.20/0.98  
% 2.20/0.98  --superposition_flag                    true
% 2.20/0.98  --sup_passive_queue_type                priority_queues
% 2.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.20/0.98  --demod_completeness_check              fast
% 2.20/0.98  --demod_use_ground                      true
% 2.20/0.98  --sup_to_prop_solver                    passive
% 2.20/0.98  --sup_prop_simpl_new                    true
% 2.20/0.98  --sup_prop_simpl_given                  true
% 2.20/0.98  --sup_fun_splitting                     false
% 2.20/0.98  --sup_smt_interval                      50000
% 2.20/0.98  
% 2.20/0.98  ------ Superposition Simplification Setup
% 2.20/0.98  
% 2.20/0.98  --sup_indices_passive                   []
% 2.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_full_bw                           [BwDemod]
% 2.20/0.98  --sup_immed_triv                        [TrivRules]
% 2.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_immed_bw_main                     []
% 2.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/0.98  
% 2.20/0.98  ------ Combination Options
% 2.20/0.98  
% 2.20/0.98  --comb_res_mult                         3
% 2.20/0.98  --comb_sup_mult                         2
% 2.20/0.98  --comb_inst_mult                        10
% 2.20/0.98  
% 2.20/0.98  ------ Debug Options
% 2.20/0.98  
% 2.20/0.98  --dbg_backtrace                         false
% 2.20/0.98  --dbg_dump_prop_clauses                 false
% 2.20/0.98  --dbg_dump_prop_clauses_file            -
% 2.20/0.98  --dbg_out_stat                          false
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  ------ Proving...
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  % SZS status Theorem for theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  fof(f20,conjecture,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f21,negated_conjecture,(
% 2.20/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.20/0.98    inference(negated_conjecture,[],[f20])).
% 2.20/0.98  
% 2.20/0.98  fof(f37,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f21])).
% 2.20/0.98  
% 2.20/0.98  fof(f38,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f37])).
% 2.20/0.98  
% 2.20/0.98  fof(f41,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(nnf_transformation,[],[f38])).
% 2.20/0.98  
% 2.20/0.98  fof(f42,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f41])).
% 2.20/0.98  
% 2.20/0.98  fof(f45,plain,(
% 2.20/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f44,plain,(
% 2.20/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f43,plain,(
% 2.20/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f46,plain,(
% 2.20/0.98    ((k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f45,f44,f43])).
% 2.20/0.98  
% 2.20/0.98  fof(f72,plain,(
% 2.20/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f16,axiom,(
% 2.20/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f30,plain,(
% 2.20/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.20/0.98    inference(ennf_transformation,[],[f16])).
% 2.20/0.98  
% 2.20/0.98  fof(f62,plain,(
% 2.20/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f30])).
% 2.20/0.98  
% 2.20/0.98  fof(f15,axiom,(
% 2.20/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f29,plain,(
% 2.20/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.20/0.98    inference(ennf_transformation,[],[f15])).
% 2.20/0.98  
% 2.20/0.98  fof(f61,plain,(
% 2.20/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f29])).
% 2.20/0.98  
% 2.20/0.98  fof(f71,plain,(
% 2.20/0.98    l1_pre_topc(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f4,axiom,(
% 2.20/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f50,plain,(
% 2.20/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.20/0.98    inference(cnf_transformation,[],[f4])).
% 2.20/0.98  
% 2.20/0.98  fof(f7,axiom,(
% 2.20/0.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f53,plain,(
% 2.20/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.20/0.98    inference(cnf_transformation,[],[f7])).
% 2.20/0.98  
% 2.20/0.98  fof(f3,axiom,(
% 2.20/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f49,plain,(
% 2.20/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f3])).
% 2.20/0.98  
% 2.20/0.98  fof(f78,plain,(
% 2.20/0.98    k1_xboole_0 = sK3),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f79,plain,(
% 2.20/0.98    ( ! [X0] : (k1_subset_1(X0) = sK3) )),
% 2.20/0.98    inference(definition_unfolding,[],[f49,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f80,plain,(
% 2.20/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK3)) )),
% 2.20/0.98    inference(definition_unfolding,[],[f53,f79])).
% 2.20/0.98  
% 2.20/0.98  fof(f83,plain,(
% 2.20/0.98    ( ! [X0] : (k3_subset_1(X0,sK3) = X0) )),
% 2.20/0.98    inference(definition_unfolding,[],[f50,f80])).
% 2.20/0.98  
% 2.20/0.98  fof(f9,axiom,(
% 2.20/0.98    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f23,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 2.20/0.98    inference(ennf_transformation,[],[f9])).
% 2.20/0.98  
% 2.20/0.98  fof(f24,plain,(
% 2.20/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 2.20/0.98    inference(flattening,[],[f23])).
% 2.20/0.98  
% 2.20/0.98  fof(f55,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 2.20/0.98    inference(cnf_transformation,[],[f24])).
% 2.20/0.98  
% 2.20/0.98  fof(f86,plain,(
% 2.20/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK3 = X0) )),
% 2.20/0.98    inference(definition_unfolding,[],[f55,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f8,axiom,(
% 2.20/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f54,plain,(
% 2.20/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.20/0.98    inference(cnf_transformation,[],[f8])).
% 2.20/0.98  
% 2.20/0.98  fof(f85,plain,(
% 2.20/0.98    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(X0))) )),
% 2.20/0.98    inference(definition_unfolding,[],[f54,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f18,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f33,plain,(
% 2.20/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f18])).
% 2.20/0.98  
% 2.20/0.98  fof(f34,plain,(
% 2.20/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.98    inference(flattening,[],[f33])).
% 2.20/0.98  
% 2.20/0.98  fof(f64,plain,(
% 2.20/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f34])).
% 2.20/0.98  
% 2.20/0.98  fof(f70,plain,(
% 2.20/0.98    v2_pre_topc(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f17,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f31,plain,(
% 2.20/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f17])).
% 2.20/0.98  
% 2.20/0.98  fof(f32,plain,(
% 2.20/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.20/0.98    inference(flattening,[],[f31])).
% 2.20/0.98  
% 2.20/0.98  fof(f63,plain,(
% 2.20/0.98    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f32])).
% 2.20/0.98  
% 2.20/0.98  fof(f2,axiom,(
% 2.20/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f48,plain,(
% 2.20/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f2])).
% 2.20/0.98  
% 2.20/0.98  fof(f82,plain,(
% 2.20/0.98    ( ! [X0] : (r1_tarski(sK3,X0)) )),
% 2.20/0.98    inference(definition_unfolding,[],[f48,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f14,axiom,(
% 2.20/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f28,plain,(
% 2.20/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.20/0.98    inference(ennf_transformation,[],[f14])).
% 2.20/0.98  
% 2.20/0.98  fof(f60,plain,(
% 2.20/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f28])).
% 2.20/0.98  
% 2.20/0.98  fof(f77,plain,(
% 2.20/0.98    ( ! [X3] : (r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f5,axiom,(
% 2.20/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f51,plain,(
% 2.20/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.20/0.98    inference(cnf_transformation,[],[f5])).
% 2.20/0.98  
% 2.20/0.98  fof(f84,plain,(
% 2.20/0.98    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0))) )),
% 2.20/0.98    inference(definition_unfolding,[],[f51,f80])).
% 2.20/0.98  
% 2.20/0.98  fof(f19,axiom,(
% 2.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f35,plain,(
% 2.20/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f19])).
% 2.20/0.98  
% 2.20/0.98  fof(f36,plain,(
% 2.20/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(flattening,[],[f35])).
% 2.20/0.98  
% 2.20/0.98  fof(f39,plain,(
% 2.20/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.20/0.98    introduced(choice_axiom,[])).
% 2.20/0.98  
% 2.20/0.98  fof(f40,plain,(
% 2.20/0.98    ! [X0] : ((v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).
% 2.20/0.98  
% 2.20/0.98  fof(f65,plain,(
% 2.20/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f40])).
% 2.20/0.98  
% 2.20/0.98  fof(f69,plain,(
% 2.20/0.98    ~v2_struct_0(sK1)),
% 2.20/0.98    inference(cnf_transformation,[],[f46])).
% 2.20/0.98  
% 2.20/0.98  fof(f13,axiom,(
% 2.20/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f27,plain,(
% 2.20/0.98    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.98    inference(ennf_transformation,[],[f13])).
% 2.20/0.98  
% 2.20/0.98  fof(f59,plain,(
% 2.20/0.98    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.98    inference(cnf_transformation,[],[f27])).
% 2.20/0.98  
% 2.20/0.98  fof(f12,axiom,(
% 2.20/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f58,plain,(
% 2.20/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.20/0.98    inference(cnf_transformation,[],[f12])).
% 2.20/0.98  
% 2.20/0.98  fof(f88,plain,(
% 2.20/0.98    k6_relat_1(sK3) = sK3),
% 2.20/0.98    inference(definition_unfolding,[],[f58,f78,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f11,axiom,(
% 2.20/0.98    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f57,plain,(
% 2.20/0.98    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f11])).
% 2.20/0.98  
% 2.20/0.98  fof(f87,plain,(
% 2.20/0.98    ( ! [X0] : (k9_relat_1(sK3,X0) = sK3) )),
% 2.20/0.98    inference(definition_unfolding,[],[f57,f78,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f1,axiom,(
% 2.20/0.98    v1_xboole_0(k1_xboole_0)),
% 2.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/0.98  
% 2.20/0.98  fof(f47,plain,(
% 2.20/0.98    v1_xboole_0(k1_xboole_0)),
% 2.20/0.98    inference(cnf_transformation,[],[f1])).
% 2.20/0.98  
% 2.20/0.98  fof(f81,plain,(
% 2.20/0.98    v1_xboole_0(sK3)),
% 2.20/0.98    inference(definition_unfolding,[],[f47,f78])).
% 2.20/0.98  
% 2.20/0.98  fof(f66,plain,(
% 2.20/0.98    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.20/0.98    inference(cnf_transformation,[],[f40])).
% 2.20/0.98  
% 2.20/0.98  cnf(c_25,negated_conjecture,
% 2.20/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.20/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_768,plain,
% 2.20/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_13,plain,
% 2.20/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_12,plain,
% 2.20/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_316,plain,
% 2.20/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.20/0.98      inference(resolution,[status(thm)],[c_13,c_12]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_26,negated_conjecture,
% 2.20/0.98      ( l1_pre_topc(sK1) ),
% 2.20/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_448,plain,
% 2.20/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_316,c_26]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_449,plain,
% 2.20/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_788,plain,
% 2.20/0.98      ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
% 2.20/0.98      inference(light_normalisation,[status(thm)],[c_768,c_449]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2,negated_conjecture,
% 2.20/0.98      ( k3_subset_1(X0,sK3) = X0 ),
% 2.20/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_6,negated_conjecture,
% 2.20/0.98      ( r2_hidden(X0,X1)
% 2.20/0.98      | r2_hidden(X0,k3_subset_1(X2,X1))
% 2.20/0.98      | ~ m1_subset_1(X0,X2)
% 2.20/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.20/0.98      | sK3 = X2 ),
% 2.20/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_772,plain,
% 2.20/0.98      ( sK3 = X0
% 2.20/0.98      | r2_hidden(X1,X2) = iProver_top
% 2.20/0.98      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top
% 2.20/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.20/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1080,plain,
% 2.20/0.98      ( sK3 = X0
% 2.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 2.20/0.98      | r2_hidden(X1,sK3) = iProver_top
% 2.20/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.20/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 2.20/0.98      inference(superposition,[status(thm)],[c_2,c_772]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_5,negated_conjecture,
% 2.20/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
% 2.20/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_50,plain,
% 2.20/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1316,plain,
% 2.20/0.98      ( m1_subset_1(X1,X0) != iProver_top
% 2.20/0.98      | r2_hidden(X1,sK3) = iProver_top
% 2.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 2.20/0.98      | sK3 = X0 ),
% 2.20/0.98      inference(global_propositional_subsumption,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_1080,c_50]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1317,plain,
% 2.20/0.98      ( sK3 = X0
% 2.20/0.98      | r2_hidden(X1,X0) = iProver_top
% 2.20/0.98      | r2_hidden(X1,sK3) = iProver_top
% 2.20/0.98      | m1_subset_1(X1,X0) != iProver_top ),
% 2.20/0.98      inference(renaming,[status(thm)],[c_1316]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1480,plain,
% 2.20/0.98      ( k2_struct_0(sK1) = sK3
% 2.20/0.98      | r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
% 2.20/0.98      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.20/0.98      inference(superposition,[status(thm)],[c_788,c_1317]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_15,plain,
% 2.20/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_27,negated_conjecture,
% 2.20/0.98      ( v2_pre_topc(sK1) ),
% 2.20/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_433,plain,
% 2.20/0.98      ( v3_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_434,plain,
% 2.20/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_433]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_436,plain,
% 2.20/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1) ),
% 2.20/0.98      inference(global_propositional_subsumption,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_434,c_26]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_14,plain,
% 2.20/0.98      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1,negated_conjecture,
% 2.20/0.98      ( r1_tarski(sK3,X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_11,plain,
% 2.20/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_301,plain,
% 2.20/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK3 != X1 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_302,plain,
% 2.20/0.98      ( ~ r2_hidden(X0,sK3) ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_301]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_20,negated_conjecture,
% 2.20/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.20/0.98      | ~ v4_pre_topc(X0,sK1)
% 2.20/0.98      | r2_hidden(X0,sK3)
% 2.20/0.98      | ~ r2_hidden(sK2,X0)
% 2.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.20/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_312,plain,
% 2.20/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.20/0.98      | ~ v4_pre_topc(X0,sK1)
% 2.20/0.98      | ~ r2_hidden(sK2,X0)
% 2.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.20/0.98      inference(backward_subsumption_resolution,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_302,c_20]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_352,plain,
% 2.20/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.20/0.98      | ~ r2_hidden(sK2,X0)
% 2.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.20/0.98      | ~ v2_pre_topc(X1)
% 2.20/0.98      | ~ l1_pre_topc(X1)
% 2.20/0.98      | k2_struct_0(X1) != X0
% 2.20/0.98      | sK1 != X1 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_312]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_353,plain,
% 2.20/0.98      ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 2.20/0.98      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 2.20/0.98      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.20/0.98      | ~ v2_pre_topc(sK1)
% 2.20/0.98      | ~ l1_pre_topc(sK1) ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_352]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_355,plain,
% 2.20/0.98      ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 2.20/0.98      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 2.20/0.98      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.20/0.98      inference(global_propositional_subsumption,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_353,c_27,c_26]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_445,plain,
% 2.20/0.98      ( ~ r2_hidden(sK2,k2_struct_0(sK1))
% 2.20/0.98      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.20/0.98      inference(backward_subsumption_resolution,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_436,c_355]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_764,plain,
% 2.20/0.98      ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 2.20/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_810,plain,
% 2.20/0.98      ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 2.20/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.20/0.98      inference(light_normalisation,[status(thm)],[c_764,c_449]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_3,negated_conjecture,
% 2.20/0.98      ( m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0)) ),
% 2.20/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_775,plain,
% 2.20/0.98      ( m1_subset_1(k3_subset_1(X0,sK3),k1_zfmisc_1(X0)) = iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_799,plain,
% 2.20/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.20/0.98      inference(light_normalisation,[status(thm)],[c_775,c_2]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_813,plain,
% 2.20/0.98      ( r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 2.20/0.98      inference(forward_subsumption_resolution,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_810,c_799]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2294,plain,
% 2.20/0.98      ( k2_struct_0(sK1) = sK3 | r2_hidden(sK2,sK3) = iProver_top ),
% 2.20/0.98      inference(global_propositional_subsumption,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_1480,c_813]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_767,plain,
% 2.20/0.98      ( r2_hidden(X0,sK3) != iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2300,plain,
% 2.20/0.98      ( k2_struct_0(sK1) = sK3 ),
% 2.20/0.98      inference(forward_subsumption_resolution,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_2294,c_767]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_19,plain,
% 2.20/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/0.98      | v2_struct_0(X0)
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0) ),
% 2.20/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_28,negated_conjecture,
% 2.20/0.98      ( ~ v2_struct_0(sK1) ),
% 2.20/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_402,plain,
% 2.20/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0)
% 2.20/0.98      | sK1 != X0 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_403,plain,
% 2.20/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.20/0.98      | ~ v2_pre_topc(sK1)
% 2.20/0.98      | ~ l1_pre_topc(sK1) ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_405,plain,
% 2.20/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.20/0.98      inference(global_propositional_subsumption,
% 2.20/0.98                [status(thm)],
% 2.20/0.98                [c_403,c_27,c_26]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_766,plain,
% 2.20/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_795,plain,
% 2.20/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.20/0.98      inference(light_normalisation,[status(thm)],[c_766,c_449]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_10,plain,
% 2.20/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.20/0.98      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.20/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_770,plain,
% 2.20/0.98      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 2.20/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.20/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_1657,plain,
% 2.20/0.98      ( k9_relat_1(k6_relat_1(k2_struct_0(sK1)),sK0(sK1)) = sK0(sK1) ),
% 2.20/0.98      inference(superposition,[status(thm)],[c_795,c_770]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2303,plain,
% 2.20/0.98      ( k9_relat_1(k6_relat_1(sK3),sK0(sK1)) = sK0(sK1) ),
% 2.20/0.98      inference(demodulation,[status(thm)],[c_2300,c_1657]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_9,negated_conjecture,
% 2.20/0.98      ( k6_relat_1(sK3) = sK3 ),
% 2.20/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2316,plain,
% 2.20/0.98      ( k9_relat_1(sK3,sK0(sK1)) = sK0(sK1) ),
% 2.20/0.98      inference(light_normalisation,[status(thm)],[c_2303,c_9]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_8,negated_conjecture,
% 2.20/0.98      ( k9_relat_1(sK3,X0) = sK3 ),
% 2.20/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_2317,plain,
% 2.20/0.98      ( sK0(sK1) = sK3 ),
% 2.20/0.98      inference(demodulation,[status(thm)],[c_2316,c_8]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_0,negated_conjecture,
% 2.20/0.98      ( v1_xboole_0(sK3) ),
% 2.20/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_18,plain,
% 2.20/0.98      ( v2_struct_0(X0)
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0)
% 2.20/0.98      | ~ v1_xboole_0(sK0(X0)) ),
% 2.20/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_330,plain,
% 2.20/0.98      ( v2_struct_0(X0)
% 2.20/0.98      | ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0)
% 2.20/0.98      | sK0(X0) != sK3 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_394,plain,
% 2.20/0.98      ( ~ v2_pre_topc(X0)
% 2.20/0.98      | ~ l1_pre_topc(X0)
% 2.20/0.98      | sK0(X0) != sK3
% 2.20/0.98      | sK1 != X0 ),
% 2.20/0.98      inference(resolution_lifted,[status(thm)],[c_330,c_28]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(c_395,plain,
% 2.20/0.98      ( ~ v2_pre_topc(sK1) | ~ l1_pre_topc(sK1) | sK0(sK1) != sK3 ),
% 2.20/0.98      inference(unflattening,[status(thm)],[c_394]) ).
% 2.20/0.98  
% 2.20/0.98  cnf(contradiction,plain,
% 2.20/0.98      ( $false ),
% 2.20/0.98      inference(minisat,[status(thm)],[c_2317,c_395,c_26,c_27]) ).
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/0.98  
% 2.20/0.98  ------                               Statistics
% 2.20/0.98  
% 2.20/0.98  ------ General
% 2.20/0.98  
% 2.20/0.98  abstr_ref_over_cycles:                  0
% 2.20/0.98  abstr_ref_under_cycles:                 0
% 2.20/0.98  gc_basic_clause_elim:                   0
% 2.20/0.98  forced_gc_time:                         0
% 2.20/0.98  parsing_time:                           0.009
% 2.20/0.98  unif_index_cands_time:                  0.
% 2.20/0.98  unif_index_add_time:                    0.
% 2.20/0.98  orderings_time:                         0.
% 2.20/0.98  out_proof_time:                         0.011
% 2.20/0.98  total_time:                             0.11
% 2.20/0.98  num_of_symbols:                         51
% 2.20/0.98  num_of_terms:                           2187
% 2.20/0.98  
% 2.20/0.98  ------ Preprocessing
% 2.20/0.98  
% 2.20/0.98  num_of_splits:                          0
% 2.20/0.98  num_of_split_atoms:                     0
% 2.20/0.98  num_of_reused_defs:                     0
% 2.20/0.98  num_eq_ax_congr_red:                    10
% 2.20/0.98  num_of_sem_filtered_clauses:            1
% 2.20/0.98  num_of_subtypes:                        0
% 2.20/0.98  monotx_restored_types:                  0
% 2.20/0.98  sat_num_of_epr_types:                   0
% 2.20/0.98  sat_num_of_non_cyclic_types:            0
% 2.20/0.98  sat_guarded_non_collapsed_types:        0
% 2.20/0.98  num_pure_diseq_elim:                    0
% 2.20/0.98  simp_replaced_by:                       0
% 2.20/0.98  res_preprocessed:                       103
% 2.20/0.98  prep_upred:                             0
% 2.20/0.98  prep_unflattend:                        11
% 2.20/0.98  smt_new_axioms:                         0
% 2.20/0.98  pred_elim_cands:                        2
% 2.20/0.98  pred_elim:                              8
% 2.20/0.98  pred_elim_cl:                           12
% 2.20/0.98  pred_elim_cycles:                       10
% 2.20/0.98  merged_defs:                            0
% 2.20/0.98  merged_defs_ncl:                        0
% 2.20/0.98  bin_hyper_res:                          0
% 2.20/0.98  prep_cycles:                            4
% 2.20/0.98  pred_elim_time:                         0.003
% 2.20/0.98  splitting_time:                         0.
% 2.20/0.98  sem_filter_time:                        0.
% 2.20/0.98  monotx_time:                            0.
% 2.20/0.98  subtype_inf_time:                       0.
% 2.20/0.98  
% 2.20/0.98  ------ Problem properties
% 2.20/0.98  
% 2.20/0.98  clauses:                                17
% 2.20/0.98  conjectures:                            8
% 2.20/0.98  epr:                                    1
% 2.20/0.98  horn:                                   16
% 2.20/0.98  ground:                                 8
% 2.20/0.98  unary:                                  12
% 2.20/0.98  binary:                                 3
% 2.20/0.98  lits:                                   26
% 2.20/0.98  lits_eq:                                8
% 2.20/0.98  fd_pure:                                0
% 2.20/0.98  fd_pseudo:                              0
% 2.20/0.98  fd_cond:                                1
% 2.20/0.98  fd_pseudo_cond:                         0
% 2.20/0.98  ac_symbols:                             0
% 2.20/0.98  
% 2.20/0.98  ------ Propositional Solver
% 2.20/0.98  
% 2.20/0.98  prop_solver_calls:                      27
% 2.20/0.98  prop_fast_solver_calls:                 492
% 2.20/0.98  smt_solver_calls:                       0
% 2.20/0.98  smt_fast_solver_calls:                  0
% 2.20/0.98  prop_num_of_clauses:                    862
% 2.20/0.98  prop_preprocess_simplified:             3657
% 2.20/0.98  prop_fo_subsumed:                       16
% 2.20/0.98  prop_solver_time:                       0.
% 2.20/0.98  smt_solver_time:                        0.
% 2.20/0.98  smt_fast_solver_time:                   0.
% 2.20/0.98  prop_fast_solver_time:                  0.
% 2.20/0.98  prop_unsat_core_time:                   0.
% 2.20/0.98  
% 2.20/0.98  ------ QBF
% 2.20/0.98  
% 2.20/0.98  qbf_q_res:                              0
% 2.20/0.98  qbf_num_tautologies:                    0
% 2.20/0.98  qbf_prep_cycles:                        0
% 2.20/0.98  
% 2.20/0.98  ------ BMC1
% 2.20/0.98  
% 2.20/0.98  bmc1_current_bound:                     -1
% 2.20/0.98  bmc1_last_solved_bound:                 -1
% 2.20/0.98  bmc1_unsat_core_size:                   -1
% 2.20/0.98  bmc1_unsat_core_parents_size:           -1
% 2.20/0.98  bmc1_merge_next_fun:                    0
% 2.20/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.20/0.98  
% 2.20/0.98  ------ Instantiation
% 2.20/0.98  
% 2.20/0.98  inst_num_of_clauses:                    257
% 2.20/0.98  inst_num_in_passive:                    135
% 2.20/0.98  inst_num_in_active:                     120
% 2.20/0.98  inst_num_in_unprocessed:                2
% 2.20/0.98  inst_num_of_loops:                      140
% 2.20/0.98  inst_num_of_learning_restarts:          0
% 2.20/0.98  inst_num_moves_active_passive:          18
% 2.20/0.98  inst_lit_activity:                      0
% 2.20/0.98  inst_lit_activity_moves:                0
% 2.20/0.98  inst_num_tautologies:                   0
% 2.20/0.98  inst_num_prop_implied:                  0
% 2.20/0.98  inst_num_existing_simplified:           0
% 2.20/0.98  inst_num_eq_res_simplified:             0
% 2.20/0.98  inst_num_child_elim:                    0
% 2.20/0.98  inst_num_of_dismatching_blockings:      56
% 2.20/0.98  inst_num_of_non_proper_insts:           174
% 2.20/0.98  inst_num_of_duplicates:                 0
% 2.20/0.98  inst_inst_num_from_inst_to_res:         0
% 2.20/0.98  inst_dismatching_checking_time:         0.
% 2.20/0.98  
% 2.20/0.98  ------ Resolution
% 2.20/0.98  
% 2.20/0.98  res_num_of_clauses:                     0
% 2.20/0.98  res_num_in_passive:                     0
% 2.20/0.98  res_num_in_active:                      0
% 2.20/0.98  res_num_of_loops:                       107
% 2.20/0.98  res_forward_subset_subsumed:            18
% 2.20/0.98  res_backward_subset_subsumed:           1
% 2.20/0.98  res_forward_subsumed:                   0
% 2.20/0.98  res_backward_subsumed:                  2
% 2.20/0.98  res_forward_subsumption_resolution:     0
% 2.20/0.98  res_backward_subsumption_resolution:    4
% 2.20/0.98  res_clause_to_clause_subsumption:       72
% 2.20/0.98  res_orphan_elimination:                 0
% 2.20/0.98  res_tautology_del:                      8
% 2.20/0.98  res_num_eq_res_simplified:              0
% 2.20/0.98  res_num_sel_changes:                    0
% 2.20/0.98  res_moves_from_active_to_pass:          0
% 2.20/0.98  
% 2.20/0.98  ------ Superposition
% 2.20/0.98  
% 2.20/0.98  sup_time_total:                         0.
% 2.20/0.98  sup_time_generating:                    0.
% 2.20/0.98  sup_time_sim_full:                      0.
% 2.20/0.98  sup_time_sim_immed:                     0.
% 2.20/0.98  
% 2.20/0.98  sup_num_of_clauses:                     25
% 2.20/0.98  sup_num_in_active:                      19
% 2.20/0.98  sup_num_in_passive:                     6
% 2.20/0.98  sup_num_of_loops:                       26
% 2.20/0.98  sup_fw_superposition:                   12
% 2.20/0.98  sup_bw_superposition:                   9
% 2.20/0.98  sup_immediate_simplified:               12
% 2.20/0.98  sup_given_eliminated:                   0
% 2.20/0.98  comparisons_done:                       0
% 2.20/0.98  comparisons_avoided:                    0
% 2.20/0.98  
% 2.20/0.98  ------ Simplifications
% 2.20/0.98  
% 2.20/0.98  
% 2.20/0.98  sim_fw_subset_subsumed:                 3
% 2.20/0.98  sim_bw_subset_subsumed:                 2
% 2.20/0.98  sim_fw_subsumed:                        5
% 2.20/0.98  sim_bw_subsumed:                        0
% 2.20/0.98  sim_fw_subsumption_res:                 2
% 2.20/0.98  sim_bw_subsumption_res:                 0
% 2.20/0.98  sim_tautology_del:                      0
% 2.20/0.98  sim_eq_tautology_del:                   1
% 2.20/0.98  sim_eq_res_simp:                        0
% 2.20/0.98  sim_fw_demodulated:                     2
% 2.20/0.98  sim_bw_demodulated:                     9
% 2.20/0.98  sim_light_normalised:                   9
% 2.20/0.98  sim_joinable_taut:                      0
% 2.20/0.98  sim_joinable_simp:                      0
% 2.20/0.98  sim_ac_normalised:                      0
% 2.20/0.98  sim_smt_subsumption:                    0
% 2.20/0.98  
%------------------------------------------------------------------------------
