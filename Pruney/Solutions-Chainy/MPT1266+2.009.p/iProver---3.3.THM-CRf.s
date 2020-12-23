%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:59 EST 2020

% Result     : Theorem 27.27s
% Output     : CNFRefutation 27.27s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 934 expanded)
%              Number of clauses        :   79 ( 262 expanded)
%              Number of leaves         :   24 ( 223 expanded)
%              Depth                    :   22
%              Number of atoms          :  389 (3069 expanded)
%              Number of equality atoms :  180 (1177 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_xboole_0 != k1_tops_1(X0,sK1)
          | ~ v2_tops_1(sK1,X0) )
        & ( k1_xboole_0 = k1_tops_1(X0,sK1)
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f81])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_86560,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_895,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_289,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_339,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_289,c_21])).

cnf(c_340,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_904,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_895,c_340])).

cnf(c_897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_893,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_893,c_340])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_896,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1628,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_896])).

cnf(c_1810,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_1628])).

cnf(c_7285,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_904,c_1810])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_894,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_907,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_894,c_340])).

cnf(c_1038,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_904,c_907])).

cnf(c_7295,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7285,c_1038])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_898,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_898,c_5])).

cnf(c_1627,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_905,c_896])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_899,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2379,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_905,c_899])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_902,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_901,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2304,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_902,c_901])).

cnf(c_2381,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2379,c_2304])).

cnf(c_2389,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1627,c_1627,c_2381])).

cnf(c_17,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_174,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_319,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_174])).

cnf(c_320,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_322,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_21,c_20])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_344,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_345,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_345])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_892,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_908,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_892,c_340])).

cnf(c_1231,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_908])).

cnf(c_4582,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_904])).

cnf(c_4583,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_4582])).

cnf(c_4585,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4583,c_1038])).

cnf(c_4587,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4585,c_2381])).

cnf(c_7296,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_7295,c_2389,c_4587])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_172,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_305,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_172])).

cnf(c_306,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_308,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_21,c_20])).

cnf(c_14,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_359,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_360,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_360])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_891,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_909,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_891,c_340])).

cnf(c_919,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_909])).

cnf(c_911,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_904])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86560,c_7296,c_4587,c_919,c_911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.27/3.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.27/3.96  
% 27.27/3.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.27/3.96  
% 27.27/3.96  ------  iProver source info
% 27.27/3.96  
% 27.27/3.96  git: date: 2020-06-30 10:37:57 +0100
% 27.27/3.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.27/3.96  git: non_committed_changes: false
% 27.27/3.96  git: last_make_outside_of_git: false
% 27.27/3.96  
% 27.27/3.96  ------ 
% 27.27/3.96  
% 27.27/3.96  ------ Input Options
% 27.27/3.96  
% 27.27/3.96  --out_options                           all
% 27.27/3.96  --tptp_safe_out                         true
% 27.27/3.96  --problem_path                          ""
% 27.27/3.96  --include_path                          ""
% 27.27/3.96  --clausifier                            res/vclausify_rel
% 27.27/3.96  --clausifier_options                    ""
% 27.27/3.96  --stdin                                 false
% 27.27/3.96  --stats_out                             all
% 27.27/3.96  
% 27.27/3.96  ------ General Options
% 27.27/3.96  
% 27.27/3.96  --fof                                   false
% 27.27/3.96  --time_out_real                         305.
% 27.27/3.96  --time_out_virtual                      -1.
% 27.27/3.96  --symbol_type_check                     false
% 27.27/3.96  --clausify_out                          false
% 27.27/3.96  --sig_cnt_out                           false
% 27.27/3.96  --trig_cnt_out                          false
% 27.27/3.96  --trig_cnt_out_tolerance                1.
% 27.27/3.96  --trig_cnt_out_sk_spl                   false
% 27.27/3.96  --abstr_cl_out                          false
% 27.27/3.96  
% 27.27/3.96  ------ Global Options
% 27.27/3.96  
% 27.27/3.96  --schedule                              default
% 27.27/3.96  --add_important_lit                     false
% 27.27/3.96  --prop_solver_per_cl                    1000
% 27.27/3.96  --min_unsat_core                        false
% 27.27/3.96  --soft_assumptions                      false
% 27.27/3.96  --soft_lemma_size                       3
% 27.27/3.96  --prop_impl_unit_size                   0
% 27.27/3.96  --prop_impl_unit                        []
% 27.27/3.96  --share_sel_clauses                     true
% 27.27/3.96  --reset_solvers                         false
% 27.27/3.96  --bc_imp_inh                            [conj_cone]
% 27.27/3.96  --conj_cone_tolerance                   3.
% 27.27/3.96  --extra_neg_conj                        none
% 27.27/3.96  --large_theory_mode                     true
% 27.27/3.96  --prolific_symb_bound                   200
% 27.27/3.96  --lt_threshold                          2000
% 27.27/3.96  --clause_weak_htbl                      true
% 27.27/3.96  --gc_record_bc_elim                     false
% 27.27/3.96  
% 27.27/3.96  ------ Preprocessing Options
% 27.27/3.96  
% 27.27/3.96  --preprocessing_flag                    true
% 27.27/3.96  --time_out_prep_mult                    0.1
% 27.27/3.96  --splitting_mode                        input
% 27.27/3.96  --splitting_grd                         true
% 27.27/3.96  --splitting_cvd                         false
% 27.27/3.96  --splitting_cvd_svl                     false
% 27.27/3.96  --splitting_nvd                         32
% 27.27/3.96  --sub_typing                            true
% 27.27/3.96  --prep_gs_sim                           true
% 27.27/3.96  --prep_unflatten                        true
% 27.27/3.96  --prep_res_sim                          true
% 27.27/3.96  --prep_upred                            true
% 27.27/3.96  --prep_sem_filter                       exhaustive
% 27.27/3.96  --prep_sem_filter_out                   false
% 27.27/3.96  --pred_elim                             true
% 27.27/3.96  --res_sim_input                         true
% 27.27/3.96  --eq_ax_congr_red                       true
% 27.27/3.96  --pure_diseq_elim                       true
% 27.27/3.96  --brand_transform                       false
% 27.27/3.96  --non_eq_to_eq                          false
% 27.27/3.96  --prep_def_merge                        true
% 27.27/3.96  --prep_def_merge_prop_impl              false
% 27.27/3.96  --prep_def_merge_mbd                    true
% 27.27/3.96  --prep_def_merge_tr_red                 false
% 27.27/3.96  --prep_def_merge_tr_cl                  false
% 27.27/3.96  --smt_preprocessing                     true
% 27.27/3.96  --smt_ac_axioms                         fast
% 27.27/3.96  --preprocessed_out                      false
% 27.27/3.96  --preprocessed_stats                    false
% 27.27/3.96  
% 27.27/3.96  ------ Abstraction refinement Options
% 27.27/3.96  
% 27.27/3.96  --abstr_ref                             []
% 27.27/3.96  --abstr_ref_prep                        false
% 27.27/3.96  --abstr_ref_until_sat                   false
% 27.27/3.96  --abstr_ref_sig_restrict                funpre
% 27.27/3.96  --abstr_ref_af_restrict_to_split_sk     false
% 27.27/3.96  --abstr_ref_under                       []
% 27.27/3.96  
% 27.27/3.96  ------ SAT Options
% 27.27/3.96  
% 27.27/3.96  --sat_mode                              false
% 27.27/3.96  --sat_fm_restart_options                ""
% 27.27/3.96  --sat_gr_def                            false
% 27.27/3.96  --sat_epr_types                         true
% 27.27/3.96  --sat_non_cyclic_types                  false
% 27.27/3.96  --sat_finite_models                     false
% 27.27/3.96  --sat_fm_lemmas                         false
% 27.27/3.96  --sat_fm_prep                           false
% 27.27/3.96  --sat_fm_uc_incr                        true
% 27.27/3.96  --sat_out_model                         small
% 27.27/3.96  --sat_out_clauses                       false
% 27.27/3.96  
% 27.27/3.96  ------ QBF Options
% 27.27/3.96  
% 27.27/3.96  --qbf_mode                              false
% 27.27/3.96  --qbf_elim_univ                         false
% 27.27/3.96  --qbf_dom_inst                          none
% 27.27/3.96  --qbf_dom_pre_inst                      false
% 27.27/3.96  --qbf_sk_in                             false
% 27.27/3.96  --qbf_pred_elim                         true
% 27.27/3.96  --qbf_split                             512
% 27.27/3.96  
% 27.27/3.96  ------ BMC1 Options
% 27.27/3.96  
% 27.27/3.96  --bmc1_incremental                      false
% 27.27/3.96  --bmc1_axioms                           reachable_all
% 27.27/3.96  --bmc1_min_bound                        0
% 27.27/3.96  --bmc1_max_bound                        -1
% 27.27/3.96  --bmc1_max_bound_default                -1
% 27.27/3.96  --bmc1_symbol_reachability              true
% 27.27/3.96  --bmc1_property_lemmas                  false
% 27.27/3.96  --bmc1_k_induction                      false
% 27.27/3.96  --bmc1_non_equiv_states                 false
% 27.27/3.96  --bmc1_deadlock                         false
% 27.27/3.96  --bmc1_ucm                              false
% 27.27/3.96  --bmc1_add_unsat_core                   none
% 27.27/3.96  --bmc1_unsat_core_children              false
% 27.27/3.96  --bmc1_unsat_core_extrapolate_axioms    false
% 27.27/3.96  --bmc1_out_stat                         full
% 27.27/3.96  --bmc1_ground_init                      false
% 27.27/3.96  --bmc1_pre_inst_next_state              false
% 27.27/3.96  --bmc1_pre_inst_state                   false
% 27.27/3.96  --bmc1_pre_inst_reach_state             false
% 27.27/3.96  --bmc1_out_unsat_core                   false
% 27.27/3.96  --bmc1_aig_witness_out                  false
% 27.27/3.96  --bmc1_verbose                          false
% 27.27/3.96  --bmc1_dump_clauses_tptp                false
% 27.27/3.96  --bmc1_dump_unsat_core_tptp             false
% 27.27/3.96  --bmc1_dump_file                        -
% 27.27/3.96  --bmc1_ucm_expand_uc_limit              128
% 27.27/3.96  --bmc1_ucm_n_expand_iterations          6
% 27.27/3.96  --bmc1_ucm_extend_mode                  1
% 27.27/3.96  --bmc1_ucm_init_mode                    2
% 27.27/3.96  --bmc1_ucm_cone_mode                    none
% 27.27/3.96  --bmc1_ucm_reduced_relation_type        0
% 27.27/3.96  --bmc1_ucm_relax_model                  4
% 27.27/3.96  --bmc1_ucm_full_tr_after_sat            true
% 27.27/3.96  --bmc1_ucm_expand_neg_assumptions       false
% 27.27/3.96  --bmc1_ucm_layered_model                none
% 27.27/3.96  --bmc1_ucm_max_lemma_size               10
% 27.27/3.96  
% 27.27/3.96  ------ AIG Options
% 27.27/3.96  
% 27.27/3.96  --aig_mode                              false
% 27.27/3.96  
% 27.27/3.96  ------ Instantiation Options
% 27.27/3.96  
% 27.27/3.96  --instantiation_flag                    true
% 27.27/3.96  --inst_sos_flag                         true
% 27.27/3.96  --inst_sos_phase                        true
% 27.27/3.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.27/3.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.27/3.96  --inst_lit_sel_side                     num_symb
% 27.27/3.96  --inst_solver_per_active                1400
% 27.27/3.96  --inst_solver_calls_frac                1.
% 27.27/3.96  --inst_passive_queue_type               priority_queues
% 27.27/3.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.27/3.96  --inst_passive_queues_freq              [25;2]
% 27.27/3.96  --inst_dismatching                      true
% 27.27/3.96  --inst_eager_unprocessed_to_passive     true
% 27.27/3.96  --inst_prop_sim_given                   true
% 27.27/3.96  --inst_prop_sim_new                     false
% 27.27/3.96  --inst_subs_new                         false
% 27.27/3.96  --inst_eq_res_simp                      false
% 27.27/3.96  --inst_subs_given                       false
% 27.27/3.96  --inst_orphan_elimination               true
% 27.27/3.96  --inst_learning_loop_flag               true
% 27.27/3.96  --inst_learning_start                   3000
% 27.27/3.96  --inst_learning_factor                  2
% 27.27/3.96  --inst_start_prop_sim_after_learn       3
% 27.27/3.96  --inst_sel_renew                        solver
% 27.27/3.96  --inst_lit_activity_flag                true
% 27.27/3.96  --inst_restr_to_given                   false
% 27.27/3.96  --inst_activity_threshold               500
% 27.27/3.96  --inst_out_proof                        true
% 27.27/3.96  
% 27.27/3.96  ------ Resolution Options
% 27.27/3.96  
% 27.27/3.96  --resolution_flag                       true
% 27.27/3.96  --res_lit_sel                           adaptive
% 27.27/3.96  --res_lit_sel_side                      none
% 27.27/3.96  --res_ordering                          kbo
% 27.27/3.96  --res_to_prop_solver                    active
% 27.27/3.96  --res_prop_simpl_new                    false
% 27.27/3.96  --res_prop_simpl_given                  true
% 27.27/3.96  --res_passive_queue_type                priority_queues
% 27.27/3.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.27/3.96  --res_passive_queues_freq               [15;5]
% 27.27/3.96  --res_forward_subs                      full
% 27.27/3.96  --res_backward_subs                     full
% 27.27/3.96  --res_forward_subs_resolution           true
% 27.27/3.96  --res_backward_subs_resolution          true
% 27.27/3.96  --res_orphan_elimination                true
% 27.27/3.96  --res_time_limit                        2.
% 27.27/3.96  --res_out_proof                         true
% 27.27/3.96  
% 27.27/3.96  ------ Superposition Options
% 27.27/3.96  
% 27.27/3.96  --superposition_flag                    true
% 27.27/3.96  --sup_passive_queue_type                priority_queues
% 27.27/3.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.27/3.96  --sup_passive_queues_freq               [8;1;4]
% 27.27/3.96  --demod_completeness_check              fast
% 27.27/3.96  --demod_use_ground                      true
% 27.27/3.96  --sup_to_prop_solver                    passive
% 27.27/3.96  --sup_prop_simpl_new                    true
% 27.27/3.96  --sup_prop_simpl_given                  true
% 27.27/3.96  --sup_fun_splitting                     true
% 27.27/3.96  --sup_smt_interval                      50000
% 27.27/3.96  
% 27.27/3.96  ------ Superposition Simplification Setup
% 27.27/3.96  
% 27.27/3.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.27/3.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.27/3.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.27/3.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.27/3.96  --sup_full_triv                         [TrivRules;PropSubs]
% 27.27/3.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.27/3.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.27/3.96  --sup_immed_triv                        [TrivRules]
% 27.27/3.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.96  --sup_immed_bw_main                     []
% 27.27/3.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.27/3.96  --sup_input_triv                        [Unflattening;TrivRules]
% 27.27/3.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.96  --sup_input_bw                          []
% 27.27/3.96  
% 27.27/3.96  ------ Combination Options
% 27.27/3.96  
% 27.27/3.96  --comb_res_mult                         3
% 27.27/3.96  --comb_sup_mult                         2
% 27.27/3.96  --comb_inst_mult                        10
% 27.27/3.96  
% 27.27/3.96  ------ Debug Options
% 27.27/3.96  
% 27.27/3.96  --dbg_backtrace                         false
% 27.27/3.96  --dbg_dump_prop_clauses                 false
% 27.27/3.96  --dbg_dump_prop_clauses_file            -
% 27.27/3.96  --dbg_out_stat                          false
% 27.27/3.96  ------ Parsing...
% 27.27/3.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.27/3.96  
% 27.27/3.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.27/3.96  
% 27.27/3.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.27/3.96  
% 27.27/3.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.27/3.96  ------ Proving...
% 27.27/3.96  ------ Problem Properties 
% 27.27/3.96  
% 27.27/3.96  
% 27.27/3.96  clauses                                 15
% 27.27/3.96  conjectures                             1
% 27.27/3.96  EPR                                     2
% 27.27/3.96  Horn                                    14
% 27.27/3.96  unary                                   5
% 27.27/3.96  binary                                  7
% 27.27/3.96  lits                                    28
% 27.27/3.96  lits eq                                 12
% 27.27/3.96  fd_pure                                 0
% 27.27/3.96  fd_pseudo                               0
% 27.27/3.96  fd_cond                                 0
% 27.27/3.96  fd_pseudo_cond                          1
% 27.27/3.96  AC symbols                              0
% 27.27/3.96  
% 27.27/3.96  ------ Schedule dynamic 5 is on 
% 27.27/3.96  
% 27.27/3.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.27/3.96  
% 27.27/3.96  
% 27.27/3.96  ------ 
% 27.27/3.96  Current options:
% 27.27/3.96  ------ 
% 27.27/3.96  
% 27.27/3.96  ------ Input Options
% 27.27/3.96  
% 27.27/3.96  --out_options                           all
% 27.27/3.96  --tptp_safe_out                         true
% 27.27/3.96  --problem_path                          ""
% 27.27/3.96  --include_path                          ""
% 27.27/3.96  --clausifier                            res/vclausify_rel
% 27.27/3.96  --clausifier_options                    ""
% 27.27/3.96  --stdin                                 false
% 27.27/3.96  --stats_out                             all
% 27.27/3.96  
% 27.27/3.96  ------ General Options
% 27.27/3.96  
% 27.27/3.96  --fof                                   false
% 27.27/3.96  --time_out_real                         305.
% 27.27/3.96  --time_out_virtual                      -1.
% 27.27/3.96  --symbol_type_check                     false
% 27.27/3.96  --clausify_out                          false
% 27.27/3.96  --sig_cnt_out                           false
% 27.27/3.96  --trig_cnt_out                          false
% 27.27/3.96  --trig_cnt_out_tolerance                1.
% 27.27/3.96  --trig_cnt_out_sk_spl                   false
% 27.27/3.96  --abstr_cl_out                          false
% 27.27/3.96  
% 27.27/3.96  ------ Global Options
% 27.27/3.96  
% 27.27/3.96  --schedule                              default
% 27.27/3.96  --add_important_lit                     false
% 27.27/3.96  --prop_solver_per_cl                    1000
% 27.27/3.96  --min_unsat_core                        false
% 27.27/3.96  --soft_assumptions                      false
% 27.27/3.96  --soft_lemma_size                       3
% 27.27/3.96  --prop_impl_unit_size                   0
% 27.27/3.96  --prop_impl_unit                        []
% 27.27/3.96  --share_sel_clauses                     true
% 27.27/3.96  --reset_solvers                         false
% 27.27/3.96  --bc_imp_inh                            [conj_cone]
% 27.27/3.96  --conj_cone_tolerance                   3.
% 27.27/3.96  --extra_neg_conj                        none
% 27.27/3.96  --large_theory_mode                     true
% 27.27/3.96  --prolific_symb_bound                   200
% 27.27/3.96  --lt_threshold                          2000
% 27.27/3.96  --clause_weak_htbl                      true
% 27.27/3.96  --gc_record_bc_elim                     false
% 27.27/3.96  
% 27.27/3.96  ------ Preprocessing Options
% 27.27/3.96  
% 27.27/3.96  --preprocessing_flag                    true
% 27.27/3.96  --time_out_prep_mult                    0.1
% 27.27/3.96  --splitting_mode                        input
% 27.27/3.96  --splitting_grd                         true
% 27.27/3.96  --splitting_cvd                         false
% 27.27/3.96  --splitting_cvd_svl                     false
% 27.27/3.96  --splitting_nvd                         32
% 27.27/3.96  --sub_typing                            true
% 27.27/3.96  --prep_gs_sim                           true
% 27.27/3.96  --prep_unflatten                        true
% 27.27/3.96  --prep_res_sim                          true
% 27.27/3.96  --prep_upred                            true
% 27.27/3.96  --prep_sem_filter                       exhaustive
% 27.27/3.96  --prep_sem_filter_out                   false
% 27.27/3.96  --pred_elim                             true
% 27.27/3.96  --res_sim_input                         true
% 27.27/3.96  --eq_ax_congr_red                       true
% 27.27/3.96  --pure_diseq_elim                       true
% 27.27/3.96  --brand_transform                       false
% 27.27/3.96  --non_eq_to_eq                          false
% 27.27/3.96  --prep_def_merge                        true
% 27.27/3.96  --prep_def_merge_prop_impl              false
% 27.27/3.96  --prep_def_merge_mbd                    true
% 27.27/3.96  --prep_def_merge_tr_red                 false
% 27.27/3.96  --prep_def_merge_tr_cl                  false
% 27.27/3.96  --smt_preprocessing                     true
% 27.27/3.96  --smt_ac_axioms                         fast
% 27.27/3.96  --preprocessed_out                      false
% 27.27/3.96  --preprocessed_stats                    false
% 27.27/3.96  
% 27.27/3.96  ------ Abstraction refinement Options
% 27.27/3.96  
% 27.27/3.96  --abstr_ref                             []
% 27.27/3.96  --abstr_ref_prep                        false
% 27.27/3.96  --abstr_ref_until_sat                   false
% 27.27/3.96  --abstr_ref_sig_restrict                funpre
% 27.27/3.96  --abstr_ref_af_restrict_to_split_sk     false
% 27.27/3.96  --abstr_ref_under                       []
% 27.27/3.96  
% 27.27/3.96  ------ SAT Options
% 27.27/3.96  
% 27.27/3.96  --sat_mode                              false
% 27.27/3.96  --sat_fm_restart_options                ""
% 27.27/3.96  --sat_gr_def                            false
% 27.27/3.96  --sat_epr_types                         true
% 27.27/3.96  --sat_non_cyclic_types                  false
% 27.27/3.97  --sat_finite_models                     false
% 27.27/3.97  --sat_fm_lemmas                         false
% 27.27/3.97  --sat_fm_prep                           false
% 27.27/3.97  --sat_fm_uc_incr                        true
% 27.27/3.97  --sat_out_model                         small
% 27.27/3.97  --sat_out_clauses                       false
% 27.27/3.97  
% 27.27/3.97  ------ QBF Options
% 27.27/3.97  
% 27.27/3.97  --qbf_mode                              false
% 27.27/3.97  --qbf_elim_univ                         false
% 27.27/3.97  --qbf_dom_inst                          none
% 27.27/3.97  --qbf_dom_pre_inst                      false
% 27.27/3.97  --qbf_sk_in                             false
% 27.27/3.97  --qbf_pred_elim                         true
% 27.27/3.97  --qbf_split                             512
% 27.27/3.97  
% 27.27/3.97  ------ BMC1 Options
% 27.27/3.97  
% 27.27/3.97  --bmc1_incremental                      false
% 27.27/3.97  --bmc1_axioms                           reachable_all
% 27.27/3.97  --bmc1_min_bound                        0
% 27.27/3.97  --bmc1_max_bound                        -1
% 27.27/3.97  --bmc1_max_bound_default                -1
% 27.27/3.97  --bmc1_symbol_reachability              true
% 27.27/3.97  --bmc1_property_lemmas                  false
% 27.27/3.97  --bmc1_k_induction                      false
% 27.27/3.97  --bmc1_non_equiv_states                 false
% 27.27/3.97  --bmc1_deadlock                         false
% 27.27/3.97  --bmc1_ucm                              false
% 27.27/3.97  --bmc1_add_unsat_core                   none
% 27.27/3.97  --bmc1_unsat_core_children              false
% 27.27/3.97  --bmc1_unsat_core_extrapolate_axioms    false
% 27.27/3.97  --bmc1_out_stat                         full
% 27.27/3.97  --bmc1_ground_init                      false
% 27.27/3.97  --bmc1_pre_inst_next_state              false
% 27.27/3.97  --bmc1_pre_inst_state                   false
% 27.27/3.97  --bmc1_pre_inst_reach_state             false
% 27.27/3.97  --bmc1_out_unsat_core                   false
% 27.27/3.97  --bmc1_aig_witness_out                  false
% 27.27/3.97  --bmc1_verbose                          false
% 27.27/3.97  --bmc1_dump_clauses_tptp                false
% 27.27/3.97  --bmc1_dump_unsat_core_tptp             false
% 27.27/3.97  --bmc1_dump_file                        -
% 27.27/3.97  --bmc1_ucm_expand_uc_limit              128
% 27.27/3.97  --bmc1_ucm_n_expand_iterations          6
% 27.27/3.97  --bmc1_ucm_extend_mode                  1
% 27.27/3.97  --bmc1_ucm_init_mode                    2
% 27.27/3.97  --bmc1_ucm_cone_mode                    none
% 27.27/3.97  --bmc1_ucm_reduced_relation_type        0
% 27.27/3.97  --bmc1_ucm_relax_model                  4
% 27.27/3.97  --bmc1_ucm_full_tr_after_sat            true
% 27.27/3.97  --bmc1_ucm_expand_neg_assumptions       false
% 27.27/3.97  --bmc1_ucm_layered_model                none
% 27.27/3.97  --bmc1_ucm_max_lemma_size               10
% 27.27/3.97  
% 27.27/3.97  ------ AIG Options
% 27.27/3.97  
% 27.27/3.97  --aig_mode                              false
% 27.27/3.97  
% 27.27/3.97  ------ Instantiation Options
% 27.27/3.97  
% 27.27/3.97  --instantiation_flag                    true
% 27.27/3.97  --inst_sos_flag                         true
% 27.27/3.97  --inst_sos_phase                        true
% 27.27/3.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.27/3.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.27/3.97  --inst_lit_sel_side                     none
% 27.27/3.97  --inst_solver_per_active                1400
% 27.27/3.97  --inst_solver_calls_frac                1.
% 27.27/3.97  --inst_passive_queue_type               priority_queues
% 27.27/3.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.27/3.97  --inst_passive_queues_freq              [25;2]
% 27.27/3.97  --inst_dismatching                      true
% 27.27/3.97  --inst_eager_unprocessed_to_passive     true
% 27.27/3.97  --inst_prop_sim_given                   true
% 27.27/3.97  --inst_prop_sim_new                     false
% 27.27/3.97  --inst_subs_new                         false
% 27.27/3.97  --inst_eq_res_simp                      false
% 27.27/3.97  --inst_subs_given                       false
% 27.27/3.97  --inst_orphan_elimination               true
% 27.27/3.97  --inst_learning_loop_flag               true
% 27.27/3.97  --inst_learning_start                   3000
% 27.27/3.97  --inst_learning_factor                  2
% 27.27/3.97  --inst_start_prop_sim_after_learn       3
% 27.27/3.97  --inst_sel_renew                        solver
% 27.27/3.97  --inst_lit_activity_flag                true
% 27.27/3.97  --inst_restr_to_given                   false
% 27.27/3.97  --inst_activity_threshold               500
% 27.27/3.97  --inst_out_proof                        true
% 27.27/3.97  
% 27.27/3.97  ------ Resolution Options
% 27.27/3.97  
% 27.27/3.97  --resolution_flag                       false
% 27.27/3.97  --res_lit_sel                           adaptive
% 27.27/3.97  --res_lit_sel_side                      none
% 27.27/3.97  --res_ordering                          kbo
% 27.27/3.97  --res_to_prop_solver                    active
% 27.27/3.97  --res_prop_simpl_new                    false
% 27.27/3.97  --res_prop_simpl_given                  true
% 27.27/3.97  --res_passive_queue_type                priority_queues
% 27.27/3.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.27/3.97  --res_passive_queues_freq               [15;5]
% 27.27/3.97  --res_forward_subs                      full
% 27.27/3.97  --res_backward_subs                     full
% 27.27/3.97  --res_forward_subs_resolution           true
% 27.27/3.97  --res_backward_subs_resolution          true
% 27.27/3.97  --res_orphan_elimination                true
% 27.27/3.97  --res_time_limit                        2.
% 27.27/3.97  --res_out_proof                         true
% 27.27/3.97  
% 27.27/3.97  ------ Superposition Options
% 27.27/3.97  
% 27.27/3.97  --superposition_flag                    true
% 27.27/3.97  --sup_passive_queue_type                priority_queues
% 27.27/3.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.27/3.97  --sup_passive_queues_freq               [8;1;4]
% 27.27/3.97  --demod_completeness_check              fast
% 27.27/3.97  --demod_use_ground                      true
% 27.27/3.97  --sup_to_prop_solver                    passive
% 27.27/3.97  --sup_prop_simpl_new                    true
% 27.27/3.97  --sup_prop_simpl_given                  true
% 27.27/3.97  --sup_fun_splitting                     true
% 27.27/3.97  --sup_smt_interval                      50000
% 27.27/3.97  
% 27.27/3.97  ------ Superposition Simplification Setup
% 27.27/3.97  
% 27.27/3.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.27/3.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.27/3.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.27/3.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.27/3.97  --sup_full_triv                         [TrivRules;PropSubs]
% 27.27/3.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.27/3.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.27/3.97  --sup_immed_triv                        [TrivRules]
% 27.27/3.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.97  --sup_immed_bw_main                     []
% 27.27/3.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.27/3.97  --sup_input_triv                        [Unflattening;TrivRules]
% 27.27/3.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.27/3.97  --sup_input_bw                          []
% 27.27/3.97  
% 27.27/3.97  ------ Combination Options
% 27.27/3.97  
% 27.27/3.97  --comb_res_mult                         3
% 27.27/3.97  --comb_sup_mult                         2
% 27.27/3.97  --comb_inst_mult                        10
% 27.27/3.97  
% 27.27/3.97  ------ Debug Options
% 27.27/3.97  
% 27.27/3.97  --dbg_backtrace                         false
% 27.27/3.97  --dbg_dump_prop_clauses                 false
% 27.27/3.97  --dbg_dump_prop_clauses_file            -
% 27.27/3.97  --dbg_out_stat                          false
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  ------ Proving...
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  % SZS status Theorem for theBenchmark.p
% 27.27/3.97  
% 27.27/3.97  % SZS output start CNFRefutation for theBenchmark.p
% 27.27/3.97  
% 27.27/3.97  fof(f13,axiom,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f25,plain,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.27/3.97    inference(ennf_transformation,[],[f13])).
% 27.27/3.97  
% 27.27/3.97  fof(f60,plain,(
% 27.27/3.97    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f25])).
% 27.27/3.97  
% 27.27/3.97  fof(f22,conjecture,(
% 27.27/3.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f23,negated_conjecture,(
% 27.27/3.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 27.27/3.97    inference(negated_conjecture,[],[f22])).
% 27.27/3.97  
% 27.27/3.97  fof(f34,plain,(
% 27.27/3.97    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f23])).
% 27.27/3.97  
% 27.27/3.97  fof(f40,plain,(
% 27.27/3.97    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.27/3.97    inference(nnf_transformation,[],[f34])).
% 27.27/3.97  
% 27.27/3.97  fof(f41,plain,(
% 27.27/3.97    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.27/3.97    inference(flattening,[],[f40])).
% 27.27/3.97  
% 27.27/3.97  fof(f43,plain,(
% 27.27/3.97    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.27/3.97    introduced(choice_axiom,[])).
% 27.27/3.97  
% 27.27/3.97  fof(f42,plain,(
% 27.27/3.97    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 27.27/3.97    introduced(choice_axiom,[])).
% 27.27/3.97  
% 27.27/3.97  fof(f44,plain,(
% 27.27/3.97    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 27.27/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 27.27/3.97  
% 27.27/3.97  fof(f72,plain,(
% 27.27/3.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.27/3.97    inference(cnf_transformation,[],[f44])).
% 27.27/3.97  
% 27.27/3.97  fof(f18,axiom,(
% 27.27/3.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f30,plain,(
% 27.27/3.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f18])).
% 27.27/3.97  
% 27.27/3.97  fof(f65,plain,(
% 27.27/3.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f30])).
% 27.27/3.97  
% 27.27/3.97  fof(f16,axiom,(
% 27.27/3.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f27,plain,(
% 27.27/3.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f16])).
% 27.27/3.97  
% 27.27/3.97  fof(f63,plain,(
% 27.27/3.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f27])).
% 27.27/3.97  
% 27.27/3.97  fof(f71,plain,(
% 27.27/3.97    l1_pre_topc(sK0)),
% 27.27/3.97    inference(cnf_transformation,[],[f44])).
% 27.27/3.97  
% 27.27/3.97  fof(f17,axiom,(
% 27.27/3.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f28,plain,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.27/3.97    inference(ennf_transformation,[],[f17])).
% 27.27/3.97  
% 27.27/3.97  fof(f29,plain,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(flattening,[],[f28])).
% 27.27/3.97  
% 27.27/3.97  fof(f64,plain,(
% 27.27/3.97    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f29])).
% 27.27/3.97  
% 27.27/3.97  fof(f14,axiom,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f26,plain,(
% 27.27/3.97    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.27/3.97    inference(ennf_transformation,[],[f14])).
% 27.27/3.97  
% 27.27/3.97  fof(f61,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f26])).
% 27.27/3.97  
% 27.27/3.97  fof(f19,axiom,(
% 27.27/3.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f31,plain,(
% 27.27/3.97    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f19])).
% 27.27/3.97  
% 27.27/3.97  fof(f66,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f31])).
% 27.27/3.97  
% 27.27/3.97  fof(f12,axiom,(
% 27.27/3.97    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f59,plain,(
% 27.27/3.97    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f12])).
% 27.27/3.97  
% 27.27/3.97  fof(f10,axiom,(
% 27.27/3.97    ! [X0] : k2_subset_1(X0) = X0),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f57,plain,(
% 27.27/3.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 27.27/3.97    inference(cnf_transformation,[],[f10])).
% 27.27/3.97  
% 27.27/3.97  fof(f11,axiom,(
% 27.27/3.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f24,plain,(
% 27.27/3.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.27/3.97    inference(ennf_transformation,[],[f11])).
% 27.27/3.97  
% 27.27/3.97  fof(f58,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f24])).
% 27.27/3.97  
% 27.27/3.97  fof(f3,axiom,(
% 27.27/3.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f50,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f3])).
% 27.27/3.97  
% 27.27/3.97  fof(f15,axiom,(
% 27.27/3.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f62,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.27/3.97    inference(cnf_transformation,[],[f15])).
% 27.27/3.97  
% 27.27/3.97  fof(f4,axiom,(
% 27.27/3.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f51,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f4])).
% 27.27/3.97  
% 27.27/3.97  fof(f5,axiom,(
% 27.27/3.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f52,plain,(
% 27.27/3.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f5])).
% 27.27/3.97  
% 27.27/3.97  fof(f6,axiom,(
% 27.27/3.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f53,plain,(
% 27.27/3.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f6])).
% 27.27/3.97  
% 27.27/3.97  fof(f7,axiom,(
% 27.27/3.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f54,plain,(
% 27.27/3.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f7])).
% 27.27/3.97  
% 27.27/3.97  fof(f8,axiom,(
% 27.27/3.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f55,plain,(
% 27.27/3.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f8])).
% 27.27/3.97  
% 27.27/3.97  fof(f9,axiom,(
% 27.27/3.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f56,plain,(
% 27.27/3.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f9])).
% 27.27/3.97  
% 27.27/3.97  fof(f75,plain,(
% 27.27/3.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f55,f56])).
% 27.27/3.97  
% 27.27/3.97  fof(f76,plain,(
% 27.27/3.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f54,f75])).
% 27.27/3.97  
% 27.27/3.97  fof(f77,plain,(
% 27.27/3.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f53,f76])).
% 27.27/3.97  
% 27.27/3.97  fof(f78,plain,(
% 27.27/3.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f52,f77])).
% 27.27/3.97  
% 27.27/3.97  fof(f79,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f51,f78])).
% 27.27/3.97  
% 27.27/3.97  fof(f80,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.27/3.97    inference(definition_unfolding,[],[f62,f79])).
% 27.27/3.97  
% 27.27/3.97  fof(f81,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 27.27/3.97    inference(definition_unfolding,[],[f50,f80])).
% 27.27/3.97  
% 27.27/3.97  fof(f84,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.27/3.97    inference(definition_unfolding,[],[f58,f81])).
% 27.27/3.97  
% 27.27/3.97  fof(f1,axiom,(
% 27.27/3.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f35,plain,(
% 27.27/3.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.27/3.97    inference(nnf_transformation,[],[f1])).
% 27.27/3.97  
% 27.27/3.97  fof(f36,plain,(
% 27.27/3.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.27/3.97    inference(flattening,[],[f35])).
% 27.27/3.97  
% 27.27/3.97  fof(f46,plain,(
% 27.27/3.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.27/3.97    inference(cnf_transformation,[],[f36])).
% 27.27/3.97  
% 27.27/3.97  fof(f85,plain,(
% 27.27/3.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.27/3.97    inference(equality_resolution,[],[f46])).
% 27.27/3.97  
% 27.27/3.97  fof(f2,axiom,(
% 27.27/3.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f37,plain,(
% 27.27/3.97    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.27/3.97    inference(nnf_transformation,[],[f2])).
% 27.27/3.97  
% 27.27/3.97  fof(f49,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f37])).
% 27.27/3.97  
% 27.27/3.97  fof(f82,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 27.27/3.97    inference(definition_unfolding,[],[f49,f81])).
% 27.27/3.97  
% 27.27/3.97  fof(f21,axiom,(
% 27.27/3.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f33,plain,(
% 27.27/3.97    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f21])).
% 27.27/3.97  
% 27.27/3.97  fof(f39,plain,(
% 27.27/3.97    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(nnf_transformation,[],[f33])).
% 27.27/3.97  
% 27.27/3.97  fof(f69,plain,(
% 27.27/3.97    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f39])).
% 27.27/3.97  
% 27.27/3.97  fof(f73,plain,(
% 27.27/3.97    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 27.27/3.97    inference(cnf_transformation,[],[f44])).
% 27.27/3.97  
% 27.27/3.97  fof(f20,axiom,(
% 27.27/3.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 27.27/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.27/3.97  
% 27.27/3.97  fof(f32,plain,(
% 27.27/3.97    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(ennf_transformation,[],[f20])).
% 27.27/3.97  
% 27.27/3.97  fof(f38,plain,(
% 27.27/3.97    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.27/3.97    inference(nnf_transformation,[],[f32])).
% 27.27/3.97  
% 27.27/3.97  fof(f67,plain,(
% 27.27/3.97    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f38])).
% 27.27/3.97  
% 27.27/3.97  fof(f70,plain,(
% 27.27/3.97    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f39])).
% 27.27/3.97  
% 27.27/3.97  fof(f74,plain,(
% 27.27/3.97    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 27.27/3.97    inference(cnf_transformation,[],[f44])).
% 27.27/3.97  
% 27.27/3.97  fof(f68,plain,(
% 27.27/3.97    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.27/3.97    inference(cnf_transformation,[],[f38])).
% 27.27/3.97  
% 27.27/3.97  cnf(c_8,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.27/3.97      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 27.27/3.97      inference(cnf_transformation,[],[f60]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_86560,plain,
% 27.27/3.97      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
% 27.27/3.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
% 27.27/3.97      inference(instantiation,[status(thm)],[c_8]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_20,negated_conjecture,
% 27.27/3.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.27/3.97      inference(cnf_transformation,[],[f72]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_895,plain,
% 27.27/3.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_12,plain,
% 27.27/3.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f65]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_10,plain,
% 27.27/3.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f63]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_289,plain,
% 27.27/3.97      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.27/3.97      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_21,negated_conjecture,
% 27.27/3.97      ( l1_pre_topc(sK0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f71]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_339,plain,
% 27.27/3.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_289,c_21]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_340,plain,
% 27.27/3.97      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_339]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_904,plain,
% 27.27/3.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_895,c_340]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_897,plain,
% 27.27/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.27/3.97      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_11,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f64]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_386,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | sK0 != X1 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_387,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_386]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_893,plain,
% 27.27/3.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.27/3.97      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_906,plain,
% 27.27/3.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 27.27/3.97      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_893,c_340]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_9,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.27/3.97      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 27.27/3.97      inference(cnf_transformation,[],[f61]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_896,plain,
% 27.27/3.97      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 27.27/3.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1628,plain,
% 27.27/3.97      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 27.27/3.97      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_906,c_896]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1810,plain,
% 27.27/3.97      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
% 27.27/3.97      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_897,c_1628]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_7285,plain,
% 27.27/3.97      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_904,c_1810]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_13,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1)
% 27.27/3.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f66]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_374,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 27.27/3.97      | sK0 != X1 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_375,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_374]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_894,plain,
% 27.27/3.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 27.27/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_907,plain,
% 27.27/3.97      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 27.27/3.97      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_894,c_340]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1038,plain,
% 27.27/3.97      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_904,c_907]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_7295,plain,
% 27.27/3.97      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_7285,c_1038]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_7,plain,
% 27.27/3.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 27.27/3.97      inference(cnf_transformation,[],[f59]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_898,plain,
% 27.27/3.97      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_5,plain,
% 27.27/3.97      ( k2_subset_1(X0) = X0 ),
% 27.27/3.97      inference(cnf_transformation,[],[f57]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_905,plain,
% 27.27/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_898,c_5]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1627,plain,
% 27.27/3.97      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_905,c_896]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_6,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.27/3.97      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f84]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_899,plain,
% 27.27/3.97      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 27.27/3.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_2379,plain,
% 27.27/3.97      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_905,c_899]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1,plain,
% 27.27/3.97      ( r1_tarski(X0,X0) ),
% 27.27/3.97      inference(cnf_transformation,[],[f85]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_902,plain,
% 27.27/3.97      ( r1_tarski(X0,X0) = iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_3,plain,
% 27.27/3.97      ( ~ r1_tarski(X0,X1)
% 27.27/3.97      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 27.27/3.97      inference(cnf_transformation,[],[f82]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_901,plain,
% 27.27/3.97      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
% 27.27/3.97      | r1_tarski(X0,X1) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_2304,plain,
% 27.27/3.97      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_902,c_901]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_2381,plain,
% 27.27/3.97      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_2379,c_2304]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_2389,plain,
% 27.27/3.97      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_1627,c_1627,c_2381]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_17,plain,
% 27.27/3.97      ( ~ v2_tops_1(X0,X1)
% 27.27/3.97      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f69]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_19,negated_conjecture,
% 27.27/3.97      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f73]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_174,plain,
% 27.27/3.97      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(prop_impl,[status(thm)],[c_19]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_319,plain,
% 27.27/3.97      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 27.27/3.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.27/3.97      | ~ l1_pre_topc(X0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | sK1 != X1
% 27.27/3.97      | sK0 != X0 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_17,c_174]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_320,plain,
% 27.27/3.97      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 27.27/3.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | ~ l1_pre_topc(sK0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_319]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_322,plain,
% 27.27/3.97      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 27.27/3.97      inference(global_propositional_subsumption,
% 27.27/3.97                [status(thm)],
% 27.27/3.97                [c_320,c_21,c_20]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_15,plain,
% 27.27/3.97      ( ~ v1_tops_1(X0,X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1)
% 27.27/3.97      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f67]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_344,plain,
% 27.27/3.97      ( ~ v1_tops_1(X0,X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 27.27/3.97      | sK0 != X1 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_345,plain,
% 27.27/3.97      ( ~ v1_tops_1(X0,sK0)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_344]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_415,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 27.27/3.97      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 27.27/3.97      | sK0 != sK0 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_322,c_345]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_416,plain,
% 27.27/3.97      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_415]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_892,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 27.27/3.97      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_908,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 27.27/3.97      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_892,c_340]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_1231,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 27.27/3.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_897,c_908]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_4582,plain,
% 27.27/3.97      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 27.27/3.97      inference(global_propositional_subsumption,
% 27.27/3.97                [status(thm)],
% 27.27/3.97                [c_1231,c_904]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_4583,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 27.27/3.97      inference(renaming,[status(thm)],[c_4582]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_4585,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 27.27/3.97      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(superposition,[status(thm)],[c_4583,c_1038]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_4587,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 27.27/3.97      inference(demodulation,[status(thm)],[c_4585,c_2381]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_7296,plain,
% 27.27/3.97      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 27.27/3.97      inference(demodulation,[status(thm)],[c_7295,c_2389,c_4587]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_16,plain,
% 27.27/3.97      ( v2_tops_1(X0,X1)
% 27.27/3.97      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f70]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_18,negated_conjecture,
% 27.27/3.97      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f74]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_172,plain,
% 27.27/3.97      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 27.27/3.97      inference(prop_impl,[status(thm)],[c_18]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_305,plain,
% 27.27/3.97      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 27.27/3.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.27/3.97      | ~ l1_pre_topc(X0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | sK1 != X1
% 27.27/3.97      | sK0 != X0 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_16,c_172]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_306,plain,
% 27.27/3.97      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 27.27/3.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | ~ l1_pre_topc(sK0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_305]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_308,plain,
% 27.27/3.97      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 27.27/3.97      inference(global_propositional_subsumption,
% 27.27/3.97                [status(thm)],
% 27.27/3.97                [c_306,c_21,c_20]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_14,plain,
% 27.27/3.97      ( v1_tops_1(X0,X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | ~ l1_pre_topc(X1)
% 27.27/3.97      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 27.27/3.97      inference(cnf_transformation,[],[f68]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_359,plain,
% 27.27/3.97      ( v1_tops_1(X0,X1)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.27/3.97      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 27.27/3.97      | sK0 != X1 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_360,plain,
% 27.27/3.97      ( v1_tops_1(X0,sK0)
% 27.27/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_359]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_428,plain,
% 27.27/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 27.27/3.97      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 27.27/3.97      | sK0 != sK0 ),
% 27.27/3.97      inference(resolution_lifted,[status(thm)],[c_308,c_360]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_429,plain,
% 27.27/3.97      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 27.27/3.97      inference(unflattening,[status(thm)],[c_428]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_891,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
% 27.27/3.97      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_909,plain,
% 27.27/3.97      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k2_struct_0(sK0)
% 27.27/3.97      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 27.27/3.97      inference(light_normalisation,[status(thm)],[c_891,c_340]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_919,plain,
% 27.27/3.97      ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
% 27.27/3.97      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 27.27/3.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 27.27/3.97      inference(predicate_to_equality_rev,[status(thm)],[c_909]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(c_911,plain,
% 27.27/3.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
% 27.27/3.97      inference(predicate_to_equality_rev,[status(thm)],[c_904]) ).
% 27.27/3.97  
% 27.27/3.97  cnf(contradiction,plain,
% 27.27/3.97      ( $false ),
% 27.27/3.97      inference(minisat,[status(thm)],[c_86560,c_7296,c_4587,c_919,c_911]) ).
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  % SZS output end CNFRefutation for theBenchmark.p
% 27.27/3.97  
% 27.27/3.97  ------                               Statistics
% 27.27/3.97  
% 27.27/3.97  ------ General
% 27.27/3.97  
% 27.27/3.97  abstr_ref_over_cycles:                  0
% 27.27/3.97  abstr_ref_under_cycles:                 0
% 27.27/3.97  gc_basic_clause_elim:                   0
% 27.27/3.97  forced_gc_time:                         0
% 27.27/3.97  parsing_time:                           0.01
% 27.27/3.97  unif_index_cands_time:                  0.
% 27.27/3.97  unif_index_add_time:                    0.
% 27.27/3.97  orderings_time:                         0.
% 27.27/3.97  out_proof_time:                         0.013
% 27.27/3.97  total_time:                             3.273
% 27.27/3.97  num_of_symbols:                         50
% 27.27/3.97  num_of_terms:                           88593
% 27.27/3.97  
% 27.27/3.97  ------ Preprocessing
% 27.27/3.97  
% 27.27/3.97  num_of_splits:                          0
% 27.27/3.97  num_of_split_atoms:                     0
% 27.27/3.97  num_of_reused_defs:                     0
% 27.27/3.97  num_eq_ax_congr_red:                    40
% 27.27/3.97  num_of_sem_filtered_clauses:            1
% 27.27/3.97  num_of_subtypes:                        0
% 27.27/3.97  monotx_restored_types:                  0
% 27.27/3.97  sat_num_of_epr_types:                   0
% 27.27/3.97  sat_num_of_non_cyclic_types:            0
% 27.27/3.97  sat_guarded_non_collapsed_types:        0
% 27.27/3.97  num_pure_diseq_elim:                    0
% 27.27/3.97  simp_replaced_by:                       0
% 27.27/3.97  res_preprocessed:                       89
% 27.27/3.97  prep_upred:                             0
% 27.27/3.97  prep_unflattend:                        11
% 27.27/3.97  smt_new_axioms:                         0
% 27.27/3.97  pred_elim_cands:                        2
% 27.27/3.97  pred_elim:                              4
% 27.27/3.97  pred_elim_cl:                           6
% 27.27/3.97  pred_elim_cycles:                       6
% 27.27/3.97  merged_defs:                            10
% 27.27/3.97  merged_defs_ncl:                        0
% 27.27/3.97  bin_hyper_res:                          10
% 27.27/3.97  prep_cycles:                            4
% 27.27/3.97  pred_elim_time:                         0.003
% 27.27/3.97  splitting_time:                         0.
% 27.27/3.97  sem_filter_time:                        0.
% 27.27/3.97  monotx_time:                            0.001
% 27.27/3.97  subtype_inf_time:                       0.
% 27.27/3.97  
% 27.27/3.97  ------ Problem properties
% 27.27/3.97  
% 27.27/3.97  clauses:                                15
% 27.27/3.97  conjectures:                            1
% 27.27/3.97  epr:                                    2
% 27.27/3.97  horn:                                   14
% 27.27/3.97  ground:                                 4
% 27.27/3.97  unary:                                  5
% 27.27/3.97  binary:                                 7
% 27.27/3.97  lits:                                   28
% 27.27/3.97  lits_eq:                                12
% 27.27/3.97  fd_pure:                                0
% 27.27/3.97  fd_pseudo:                              0
% 27.27/3.97  fd_cond:                                0
% 27.27/3.97  fd_pseudo_cond:                         1
% 27.27/3.97  ac_symbols:                             0
% 27.27/3.97  
% 27.27/3.97  ------ Propositional Solver
% 27.27/3.97  
% 27.27/3.97  prop_solver_calls:                      49
% 27.27/3.97  prop_fast_solver_calls:                 2433
% 27.27/3.97  smt_solver_calls:                       0
% 27.27/3.97  smt_fast_solver_calls:                  0
% 27.27/3.97  prop_num_of_clauses:                    32502
% 27.27/3.97  prop_preprocess_simplified:             49816
% 27.27/3.97  prop_fo_subsumed:                       10
% 27.27/3.97  prop_solver_time:                       0.
% 27.27/3.97  smt_solver_time:                        0.
% 27.27/3.97  smt_fast_solver_time:                   0.
% 27.27/3.97  prop_fast_solver_time:                  0.
% 27.27/3.97  prop_unsat_core_time:                   0.003
% 27.27/3.97  
% 27.27/3.97  ------ QBF
% 27.27/3.97  
% 27.27/3.97  qbf_q_res:                              0
% 27.27/3.97  qbf_num_tautologies:                    0
% 27.27/3.97  qbf_prep_cycles:                        0
% 27.27/3.97  
% 27.27/3.97  ------ BMC1
% 27.27/3.97  
% 27.27/3.97  bmc1_current_bound:                     -1
% 27.27/3.97  bmc1_last_solved_bound:                 -1
% 27.27/3.97  bmc1_unsat_core_size:                   -1
% 27.27/3.97  bmc1_unsat_core_parents_size:           -1
% 27.27/3.97  bmc1_merge_next_fun:                    0
% 27.27/3.97  bmc1_unsat_core_clauses_time:           0.
% 27.27/3.97  
% 27.27/3.97  ------ Instantiation
% 27.27/3.97  
% 27.27/3.97  inst_num_of_clauses:                    4959
% 27.27/3.97  inst_num_in_passive:                    2971
% 27.27/3.97  inst_num_in_active:                     4760
% 27.27/3.97  inst_num_in_unprocessed:                20
% 27.27/3.97  inst_num_of_loops:                      5001
% 27.27/3.97  inst_num_of_learning_restarts:          1
% 27.27/3.97  inst_num_moves_active_passive:          229
% 27.27/3.97  inst_lit_activity:                      0
% 27.27/3.97  inst_lit_activity_moves:                2
% 27.27/3.97  inst_num_tautologies:                   0
% 27.27/3.97  inst_num_prop_implied:                  0
% 27.27/3.97  inst_num_existing_simplified:           0
% 27.27/3.97  inst_num_eq_res_simplified:             0
% 27.27/3.97  inst_num_child_elim:                    0
% 27.27/3.97  inst_num_of_dismatching_blockings:      5569
% 27.27/3.97  inst_num_of_non_proper_insts:           14011
% 27.27/3.97  inst_num_of_duplicates:                 0
% 27.27/3.97  inst_inst_num_from_inst_to_res:         0
% 27.27/3.97  inst_dismatching_checking_time:         0.
% 27.27/3.97  
% 27.27/3.97  ------ Resolution
% 27.27/3.97  
% 27.27/3.97  res_num_of_clauses:                     26
% 27.27/3.97  res_num_in_passive:                     26
% 27.27/3.97  res_num_in_active:                      0
% 27.27/3.97  res_num_of_loops:                       93
% 27.27/3.97  res_forward_subset_subsumed:            928
% 27.27/3.97  res_backward_subset_subsumed:           0
% 27.27/3.97  res_forward_subsumed:                   0
% 27.27/3.97  res_backward_subsumed:                  0
% 27.27/3.97  res_forward_subsumption_resolution:     0
% 27.27/3.97  res_backward_subsumption_resolution:    0
% 27.27/3.97  res_clause_to_clause_subsumption:       42218
% 27.27/3.97  res_orphan_elimination:                 0
% 27.27/3.97  res_tautology_del:                      1596
% 27.27/3.97  res_num_eq_res_simplified:              0
% 27.27/3.97  res_num_sel_changes:                    0
% 27.27/3.97  res_moves_from_active_to_pass:          0
% 27.27/3.97  
% 27.27/3.97  ------ Superposition
% 27.27/3.97  
% 27.27/3.97  sup_time_total:                         0.
% 27.27/3.97  sup_time_generating:                    0.
% 27.27/3.97  sup_time_sim_full:                      0.
% 27.27/3.97  sup_time_sim_immed:                     0.
% 27.27/3.97  
% 27.27/3.97  sup_num_of_clauses:                     4591
% 27.27/3.97  sup_num_in_active:                      984
% 27.27/3.97  sup_num_in_passive:                     3607
% 27.27/3.97  sup_num_of_loops:                       1000
% 27.27/3.97  sup_fw_superposition:                   7730
% 27.27/3.97  sup_bw_superposition:                   485
% 27.27/3.97  sup_immediate_simplified:               5409
% 27.27/3.97  sup_given_eliminated:                   0
% 27.27/3.97  comparisons_done:                       0
% 27.27/3.97  comparisons_avoided:                    6
% 27.27/3.97  
% 27.27/3.97  ------ Simplifications
% 27.27/3.97  
% 27.27/3.97  
% 27.27/3.97  sim_fw_subset_subsumed:                 14
% 27.27/3.97  sim_bw_subset_subsumed:                 275
% 27.27/3.97  sim_fw_subsumed:                        21
% 27.27/3.97  sim_bw_subsumed:                        0
% 27.27/3.97  sim_fw_subsumption_res:                 0
% 27.27/3.97  sim_bw_subsumption_res:                 0
% 27.27/3.97  sim_tautology_del:                      32
% 27.27/3.97  sim_eq_tautology_del:                   2609
% 27.27/3.97  sim_eq_res_simp:                        2
% 27.27/3.97  sim_fw_demodulated:                     738
% 27.27/3.97  sim_bw_demodulated:                     16
% 27.27/3.97  sim_light_normalised:                   5218
% 27.27/3.97  sim_joinable_taut:                      0
% 27.27/3.97  sim_joinable_simp:                      0
% 27.27/3.97  sim_ac_normalised:                      0
% 27.27/3.97  sim_smt_subsumption:                    0
% 27.27/3.97  
%------------------------------------------------------------------------------
