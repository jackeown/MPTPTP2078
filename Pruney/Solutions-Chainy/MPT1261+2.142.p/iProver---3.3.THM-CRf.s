%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:44 EST 2020

% Result     : Theorem 39.84s
% Output     : CNFRefutation 39.84s
% Verified   : 
% Statistics : Number of formulae       :  149 (2372 expanded)
%              Number of clauses        :   89 ( 688 expanded)
%              Number of leaves         :   18 ( 553 expanded)
%              Depth                    :   26
%              Number of atoms          :  347 (9049 expanded)
%              Number of equality atoms :  171 (3052 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f43,f43])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_677,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_686,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3420,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_677,c_686])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_678,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3601,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3420,c_678])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_682,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_65256,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_682])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_65276,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_65256,c_21])).

cnf(c_65277,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_65276])).

cnf(c_65282,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3601,c_65277])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_680,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1097,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_680])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_861,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_862,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_1304,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_21,c_22,c_862])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_691,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1663,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1304,c_691])).

cnf(c_2412,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1663,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2417,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2412,c_6])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1168,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_4781,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1))) = k3_tarski(k2_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)) ),
    inference(superposition,[status(thm)],[c_2417,c_1168])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_688,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_714,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_688,c_7])).

cnf(c_2119,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1304,c_714])).

cnf(c_4828,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4781,c_2119,c_2417])).

cnf(c_5012,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))))) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_4828])).

cnf(c_5014,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5012,c_2417])).

cnf(c_65430,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_65282,c_5014])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_681,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_124535,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_681])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3419,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_686])).

cnf(c_14044,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_3419])).

cnf(c_855,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_951,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14811,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14044,c_18,c_17,c_855,c_951])).

cnf(c_124538,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_124535,c_14811])).

cnf(c_124668,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_124538,c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1877,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_684])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_859,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2264,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1877,c_21,c_22,c_859])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_689,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_723,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_689,c_7])).

cnf(c_3372,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2119,c_723])).

cnf(c_3742,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_691])).

cnf(c_5135,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2264,c_3742])).

cnf(c_5250,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5135,c_0])).

cnf(c_5255,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5250,c_6])).

cnf(c_6170,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k3_tarski(k2_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_5255,c_1168])).

cnf(c_6196,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_6170,c_5255])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_687,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1167,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_687])).

cnf(c_5245,plain,
    ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5135,c_1167])).

cnf(c_5263,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5245,c_6])).

cnf(c_5475,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5263,c_714])).

cnf(c_26985,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_6196,c_5475])).

cnf(c_26987,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_26985])).

cnf(c_26989,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_26987,c_5255])).

cnf(c_124688,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_124668,c_26989])).

cnf(c_125580,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_65430,c_124688])).

cnf(c_130607,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_125580,c_124668])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_679,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3602,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3420,c_679])).

cnf(c_3612,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3602])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_945,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130607,c_125580,c_3612,c_945,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.84/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.84/5.49  
% 39.84/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.84/5.49  
% 39.84/5.49  ------  iProver source info
% 39.84/5.49  
% 39.84/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.84/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.84/5.49  git: non_committed_changes: false
% 39.84/5.49  git: last_make_outside_of_git: false
% 39.84/5.49  
% 39.84/5.49  ------ 
% 39.84/5.49  ------ Parsing...
% 39.84/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.84/5.49  
% 39.84/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.84/5.49  
% 39.84/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.84/5.49  
% 39.84/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.84/5.49  ------ Proving...
% 39.84/5.49  ------ Problem Properties 
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  clauses                                 20
% 39.84/5.49  conjectures                             5
% 39.84/5.49  EPR                                     2
% 39.84/5.49  Horn                                    19
% 39.84/5.49  unary                                   7
% 39.84/5.49  binary                                  7
% 39.84/5.49  lits                                    42
% 39.84/5.49  lits eq                                 12
% 39.84/5.49  fd_pure                                 0
% 39.84/5.49  fd_pseudo                               0
% 39.84/5.49  fd_cond                                 0
% 39.84/5.49  fd_pseudo_cond                          0
% 39.84/5.49  AC symbols                              0
% 39.84/5.49  
% 39.84/5.49  ------ Input Options Time Limit: Unbounded
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  ------ 
% 39.84/5.49  Current options:
% 39.84/5.49  ------ 
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  ------ Proving...
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  % SZS status Theorem for theBenchmark.p
% 39.84/5.49  
% 39.84/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.84/5.49  
% 39.84/5.49  fof(f16,conjecture,(
% 39.84/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f17,negated_conjecture,(
% 39.84/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.84/5.49    inference(negated_conjecture,[],[f16])).
% 39.84/5.49  
% 39.84/5.49  fof(f28,plain,(
% 39.84/5.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.84/5.49    inference(ennf_transformation,[],[f17])).
% 39.84/5.49  
% 39.84/5.49  fof(f29,plain,(
% 39.84/5.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.84/5.49    inference(flattening,[],[f28])).
% 39.84/5.49  
% 39.84/5.49  fof(f31,plain,(
% 39.84/5.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.84/5.49    inference(nnf_transformation,[],[f29])).
% 39.84/5.49  
% 39.84/5.49  fof(f32,plain,(
% 39.84/5.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.84/5.49    inference(flattening,[],[f31])).
% 39.84/5.49  
% 39.84/5.49  fof(f34,plain,(
% 39.84/5.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.84/5.49    introduced(choice_axiom,[])).
% 39.84/5.49  
% 39.84/5.49  fof(f33,plain,(
% 39.84/5.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 39.84/5.49    introduced(choice_axiom,[])).
% 39.84/5.49  
% 39.84/5.49  fof(f35,plain,(
% 39.84/5.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 39.84/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 39.84/5.49  
% 39.84/5.49  fof(f55,plain,(
% 39.84/5.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.84/5.49    inference(cnf_transformation,[],[f35])).
% 39.84/5.49  
% 39.84/5.49  fof(f10,axiom,(
% 39.84/5.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f20,plain,(
% 39.84/5.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.84/5.49    inference(ennf_transformation,[],[f10])).
% 39.84/5.49  
% 39.84/5.49  fof(f46,plain,(
% 39.84/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.84/5.49    inference(cnf_transformation,[],[f20])).
% 39.84/5.49  
% 39.84/5.49  fof(f56,plain,(
% 39.84/5.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 39.84/5.49    inference(cnf_transformation,[],[f35])).
% 39.84/5.49  
% 39.84/5.49  fof(f13,axiom,(
% 39.84/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f24,plain,(
% 39.84/5.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(ennf_transformation,[],[f13])).
% 39.84/5.49  
% 39.84/5.49  fof(f25,plain,(
% 39.84/5.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(flattening,[],[f24])).
% 39.84/5.49  
% 39.84/5.49  fof(f49,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f25])).
% 39.84/5.49  
% 39.84/5.49  fof(f54,plain,(
% 39.84/5.49    l1_pre_topc(sK0)),
% 39.84/5.49    inference(cnf_transformation,[],[f35])).
% 39.84/5.49  
% 39.84/5.49  fof(f1,axiom,(
% 39.84/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f36,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f1])).
% 39.84/5.49  
% 39.84/5.49  fof(f7,axiom,(
% 39.84/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f43,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.84/5.49    inference(cnf_transformation,[],[f7])).
% 39.84/5.49  
% 39.84/5.49  fof(f58,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.84/5.49    inference(definition_unfolding,[],[f36,f43,f43])).
% 39.84/5.49  
% 39.84/5.49  fof(f15,axiom,(
% 39.84/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f27,plain,(
% 39.84/5.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(ennf_transformation,[],[f15])).
% 39.84/5.49  
% 39.84/5.49  fof(f52,plain,(
% 39.84/5.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f27])).
% 39.84/5.49  
% 39.84/5.49  fof(f2,axiom,(
% 39.84/5.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f30,plain,(
% 39.84/5.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 39.84/5.49    inference(nnf_transformation,[],[f2])).
% 39.84/5.49  
% 39.84/5.49  fof(f38,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f30])).
% 39.84/5.49  
% 39.84/5.49  fof(f6,axiom,(
% 39.84/5.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f42,plain,(
% 39.84/5.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.84/5.49    inference(cnf_transformation,[],[f6])).
% 39.84/5.49  
% 39.84/5.49  fof(f9,axiom,(
% 39.84/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f45,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.84/5.49    inference(cnf_transformation,[],[f9])).
% 39.84/5.49  
% 39.84/5.49  fof(f8,axiom,(
% 39.84/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f44,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.84/5.49    inference(cnf_transformation,[],[f8])).
% 39.84/5.49  
% 39.84/5.49  fof(f61,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.84/5.49    inference(definition_unfolding,[],[f45,f44])).
% 39.84/5.49  
% 39.84/5.49  fof(f4,axiom,(
% 39.84/5.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f19,plain,(
% 39.84/5.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.84/5.49    inference(ennf_transformation,[],[f4])).
% 39.84/5.49  
% 39.84/5.49  fof(f40,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f19])).
% 39.84/5.49  
% 39.84/5.49  fof(f60,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 39.84/5.49    inference(definition_unfolding,[],[f40,f44])).
% 39.84/5.49  
% 39.84/5.49  fof(f14,axiom,(
% 39.84/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f26,plain,(
% 39.84/5.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(ennf_transformation,[],[f14])).
% 39.84/5.49  
% 39.84/5.49  fof(f51,plain,(
% 39.84/5.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f26])).
% 39.84/5.49  
% 39.84/5.49  fof(f11,axiom,(
% 39.84/5.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f21,plain,(
% 39.84/5.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.84/5.49    inference(ennf_transformation,[],[f11])).
% 39.84/5.49  
% 39.84/5.49  fof(f22,plain,(
% 39.84/5.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(flattening,[],[f21])).
% 39.84/5.49  
% 39.84/5.49  fof(f47,plain,(
% 39.84/5.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f22])).
% 39.84/5.49  
% 39.84/5.49  fof(f12,axiom,(
% 39.84/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f23,plain,(
% 39.84/5.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.84/5.49    inference(ennf_transformation,[],[f12])).
% 39.84/5.49  
% 39.84/5.49  fof(f48,plain,(
% 39.84/5.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f23])).
% 39.84/5.49  
% 39.84/5.49  fof(f3,axiom,(
% 39.84/5.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f18,plain,(
% 39.84/5.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 39.84/5.49    inference(ennf_transformation,[],[f3])).
% 39.84/5.49  
% 39.84/5.49  fof(f39,plain,(
% 39.84/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f18])).
% 39.84/5.49  
% 39.84/5.49  fof(f59,plain,(
% 39.84/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)) )),
% 39.84/5.49    inference(definition_unfolding,[],[f39,f44])).
% 39.84/5.49  
% 39.84/5.49  fof(f5,axiom,(
% 39.84/5.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.84/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.84/5.49  
% 39.84/5.49  fof(f41,plain,(
% 39.84/5.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f5])).
% 39.84/5.49  
% 39.84/5.49  fof(f57,plain,(
% 39.84/5.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 39.84/5.49    inference(cnf_transformation,[],[f35])).
% 39.84/5.49  
% 39.84/5.49  fof(f50,plain,(
% 39.84/5.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.84/5.49    inference(cnf_transformation,[],[f25])).
% 39.84/5.49  
% 39.84/5.49  fof(f53,plain,(
% 39.84/5.49    v2_pre_topc(sK0)),
% 39.84/5.49    inference(cnf_transformation,[],[f35])).
% 39.84/5.49  
% 39.84/5.49  cnf(c_17,negated_conjecture,
% 39.84/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.84/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_677,plain,
% 39.84/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_8,plain,
% 39.84/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.84/5.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 39.84/5.49      inference(cnf_transformation,[],[f46]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_686,plain,
% 39.84/5.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 39.84/5.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3420,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_686]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_16,negated_conjecture,
% 39.84/5.49      ( v4_pre_topc(sK1,sK0)
% 39.84/5.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f56]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_678,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.84/5.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3601,plain,
% 39.84/5.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.84/5.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_3420,c_678]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_12,plain,
% 39.84/5.49      ( ~ v4_pre_topc(X0,X1)
% 39.84/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | ~ l1_pre_topc(X1)
% 39.84/5.49      | k2_pre_topc(X1,X0) = X0 ),
% 39.84/5.49      inference(cnf_transformation,[],[f49]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_682,plain,
% 39.84/5.49      ( k2_pre_topc(X0,X1) = X1
% 39.84/5.49      | v4_pre_topc(X1,X0) != iProver_top
% 39.84/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.84/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_65256,plain,
% 39.84/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.84/5.49      | v4_pre_topc(sK1,sK0) != iProver_top
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_682]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_18,negated_conjecture,
% 39.84/5.49      ( l1_pre_topc(sK0) ),
% 39.84/5.49      inference(cnf_transformation,[],[f54]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_21,plain,
% 39.84/5.49      ( l1_pre_topc(sK0) = iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_65276,plain,
% 39.84/5.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.84/5.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.84/5.49      inference(global_propositional_subsumption,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_65256,c_21]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_65277,plain,
% 39.84/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.84/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.84/5.49      inference(renaming,[status(thm)],[c_65276]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_65282,plain,
% 39.84/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.84/5.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_3601,c_65277]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_0,plain,
% 39.84/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.84/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_14,plain,
% 39.84/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 39.84/5.49      | ~ l1_pre_topc(X1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f52]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_680,plain,
% 39.84/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.84/5.49      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 39.84/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1097,plain,
% 39.84/5.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_680]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_22,plain,
% 39.84/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_861,plain,
% 39.84/5.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 39.84/5.49      | ~ l1_pre_topc(sK0) ),
% 39.84/5.49      inference(instantiation,[status(thm)],[c_14]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_862,plain,
% 39.84/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.84/5.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1304,plain,
% 39.84/5.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 39.84/5.49      inference(global_propositional_subsumption,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_1097,c_21,c_22,c_862]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1,plain,
% 39.84/5.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.84/5.49      inference(cnf_transformation,[],[f38]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_691,plain,
% 39.84/5.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 39.84/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1663,plain,
% 39.84/5.49      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_1304,c_691]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_2412,plain,
% 39.84/5.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_1663,c_0]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_6,plain,
% 39.84/5.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.84/5.49      inference(cnf_transformation,[],[f42]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_2417,plain,
% 39.84/5.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_2412,c_6]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_7,plain,
% 39.84/5.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.84/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1168,plain,
% 39.84/5.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_4781,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1))) = k3_tarski(k2_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),sK1)) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_2417,c_1168]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_4,plain,
% 39.84/5.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 39.84/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_688,plain,
% 39.84/5.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 39.84/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_714,plain,
% 39.84/5.49      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 39.84/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_688,c_7]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_2119,plain,
% 39.84/5.49      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_1304,c_714]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_4828,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1))) = sK1 ),
% 39.84/5.49      inference(light_normalisation,[status(thm)],[c_4781,c_2119,c_2417]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5012,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))))) = sK1 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_0,c_4828]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5014,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 39.84/5.49      inference(light_normalisation,[status(thm)],[c_5012,c_2417]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_65430,plain,
% 39.84/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.84/5.49      | k5_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_65282,c_5014]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_13,plain,
% 39.84/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | ~ l1_pre_topc(X1)
% 39.84/5.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 39.84/5.49      inference(cnf_transformation,[],[f51]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_681,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 39.84/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.84/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_124535,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_681]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_9,plain,
% 39.84/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | ~ l1_pre_topc(X1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f47]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_685,plain,
% 39.84/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.84/5.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.84/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3419,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
% 39.84/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.84/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_685,c_686]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_14044,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_3419]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_855,plain,
% 39.84/5.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | ~ l1_pre_topc(sK0) ),
% 39.84/5.49      inference(instantiation,[status(thm)],[c_9]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_951,plain,
% 39.84/5.49      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 39.84/5.49      inference(instantiation,[status(thm)],[c_8]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_14811,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 39.84/5.49      inference(global_propositional_subsumption,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_14044,c_18,c_17,c_855,c_951]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_124538,plain,
% 39.84/5.49      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_124535,c_14811]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_124668,plain,
% 39.84/5.49      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(global_propositional_subsumption,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_124538,c_21]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_10,plain,
% 39.84/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 39.84/5.49      | ~ l1_pre_topc(X1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f48]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_684,plain,
% 39.84/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.84/5.49      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 39.84/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1877,plain,
% 39.84/5.49      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_677,c_684]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_858,plain,
% 39.84/5.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 39.84/5.49      | ~ l1_pre_topc(sK0) ),
% 39.84/5.49      inference(instantiation,[status(thm)],[c_10]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_859,plain,
% 39.84/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.84/5.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 39.84/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_2264,plain,
% 39.84/5.49      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 39.84/5.49      inference(global_propositional_subsumption,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_1877,c_21,c_22,c_859]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3,plain,
% 39.84/5.49      ( r1_tarski(X0,X1)
% 39.84/5.49      | ~ r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_689,plain,
% 39.84/5.49      ( r1_tarski(X0,X1) = iProver_top
% 39.84/5.49      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_723,plain,
% 39.84/5.49      ( r1_tarski(X0,X1) = iProver_top
% 39.84/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_689,c_7]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3372,plain,
% 39.84/5.49      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 39.84/5.49      | r1_tarski(sK1,X0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_2119,c_723]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3742,plain,
% 39.84/5.49      ( k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k1_xboole_0
% 39.84/5.49      | r1_tarski(sK1,X0) != iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_3372,c_691]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5135,plain,
% 39.84/5.49      ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_2264,c_3742]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5250,plain,
% 39.84/5.49      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_5135,c_0]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5255,plain,
% 39.84/5.49      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_5250,c_6]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_6170,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k3_tarski(k2_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,sK1))) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_5255,c_1168]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_6196,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) ),
% 39.84/5.49      inference(light_normalisation,[status(thm)],[c_6170,c_5255]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5,plain,
% 39.84/5.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 39.84/5.49      inference(cnf_transformation,[],[f41]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_687,plain,
% 39.84/5.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_1167,plain,
% 39.84/5.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_0,c_687]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5245,plain,
% 39.84/5.49      ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_5135,c_1167]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5263,plain,
% 39.84/5.49      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_5245,c_6]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_5475,plain,
% 39.84/5.49      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_5263,c_714]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_26985,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
% 39.84/5.49      inference(light_normalisation,[status(thm)],[c_6196,c_5475]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_26987,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))) = k2_pre_topc(sK0,sK1) ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_0,c_26985]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_26989,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.84/5.49      inference(light_normalisation,[status(thm)],[c_26987,c_5255]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_124688,plain,
% 39.84/5.49      ( k5_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_124668,c_26989]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_125580,plain,
% 39.84/5.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 39.84/5.49      inference(superposition,[status(thm)],[c_65430,c_124688]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_130607,plain,
% 39.84/5.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_125580,c_124668]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_15,negated_conjecture,
% 39.84/5.49      ( ~ v4_pre_topc(sK1,sK0)
% 39.84/5.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(cnf_transformation,[],[f57]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_679,plain,
% 39.84/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 39.84/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.84/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3602,plain,
% 39.84/5.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 39.84/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.84/5.49      inference(demodulation,[status(thm)],[c_3420,c_679]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_3612,plain,
% 39.84/5.49      ( ~ v4_pre_topc(sK1,sK0)
% 39.84/5.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 39.84/5.49      inference(predicate_to_equality_rev,[status(thm)],[c_3602]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_11,plain,
% 39.84/5.49      ( v4_pre_topc(X0,X1)
% 39.84/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.84/5.49      | ~ v2_pre_topc(X1)
% 39.84/5.49      | ~ l1_pre_topc(X1)
% 39.84/5.49      | k2_pre_topc(X1,X0) != X0 ),
% 39.84/5.49      inference(cnf_transformation,[],[f50]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_945,plain,
% 39.84/5.49      ( v4_pre_topc(sK1,sK0)
% 39.84/5.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.84/5.49      | ~ v2_pre_topc(sK0)
% 39.84/5.49      | ~ l1_pre_topc(sK0)
% 39.84/5.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 39.84/5.49      inference(instantiation,[status(thm)],[c_11]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(c_19,negated_conjecture,
% 39.84/5.49      ( v2_pre_topc(sK0) ),
% 39.84/5.49      inference(cnf_transformation,[],[f53]) ).
% 39.84/5.49  
% 39.84/5.49  cnf(contradiction,plain,
% 39.84/5.49      ( $false ),
% 39.84/5.49      inference(minisat,
% 39.84/5.49                [status(thm)],
% 39.84/5.49                [c_130607,c_125580,c_3612,c_945,c_17,c_18,c_19]) ).
% 39.84/5.49  
% 39.84/5.49  
% 39.84/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.84/5.49  
% 39.84/5.49  ------                               Statistics
% 39.84/5.49  
% 39.84/5.49  ------ Selected
% 39.84/5.49  
% 39.84/5.49  total_time:                             4.823
% 39.84/5.49  
%------------------------------------------------------------------------------
