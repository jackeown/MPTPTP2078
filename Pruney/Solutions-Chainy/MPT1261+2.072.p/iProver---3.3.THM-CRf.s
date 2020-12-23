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
% DateTime   : Thu Dec  3 12:14:34 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 862 expanded)
%              Number of clauses        :   79 ( 248 expanded)
%              Number of leaves         :   21 ( 212 expanded)
%              Depth                    :   18
%              Number of atoms          :  327 (2661 expanded)
%              Number of equality atoms :  173 (1100 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_630,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_638,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12840,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_630,c_638])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_631,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13103,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12840,c_631])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_636,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19971,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_636])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_20268,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19971,c_23])).

cnf(c_20269,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20268])).

cnf(c_20274,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_13103,c_20269])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_641,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_642,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_671,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_642,c_11])).

cnf(c_9723,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_641,c_671])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_668,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_11])).

cnf(c_13295,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_9723,c_668])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1191,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_2])).

cnf(c_1373,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1191])).

cnf(c_6,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_640,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_664,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8,c_640])).

cnf(c_1618,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_664])).

cnf(c_9727,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1618,c_671])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1205,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_11])).

cnf(c_1842,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_1205])).

cnf(c_10542,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9727,c_1842])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1207,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_3143,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1207,c_668])).

cnf(c_10599,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10542,c_3143])).

cnf(c_13313,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13295,c_10599])).

cnf(c_14340,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13313,c_8])).

cnf(c_3146,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_668])).

cnf(c_10565,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9727,c_3146])).

cnf(c_10568,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10565,c_5])).

cnf(c_14342,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_14340,c_10568])).

cnf(c_21381,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_20274,c_14342])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_639,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_700,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_639,c_8])).

cnf(c_19750,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_700])).

cnf(c_20533,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_19750])).

cnf(c_21128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20533,c_23])).

cnf(c_21129,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21128])).

cnf(c_21137,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_630,c_21129])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_633,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1769,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_633])).

cnf(c_879,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2361,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_20,c_19,c_879])).

cnf(c_21139,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_21137,c_2361])).

cnf(c_21440,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_21381,c_21139])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_634,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19995,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_634])).

cnf(c_887,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_20548,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19995,c_20,c_19,c_887])).

cnf(c_23072,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_21440,c_20548])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_876,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23072,c_21440,c_876,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.75/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.49  
% 7.75/1.49  ------  iProver source info
% 7.75/1.49  
% 7.75/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.49  git: non_committed_changes: false
% 7.75/1.49  git: last_make_outside_of_git: false
% 7.75/1.49  
% 7.75/1.49  ------ 
% 7.75/1.49  ------ Parsing...
% 7.75/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.49  ------ Proving...
% 7.75/1.49  ------ Problem Properties 
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  clauses                                 22
% 7.75/1.49  conjectures                             5
% 7.75/1.49  EPR                                     2
% 7.75/1.49  Horn                                    21
% 7.75/1.49  unary                                   12
% 7.75/1.49  binary                                  4
% 7.75/1.49  lits                                    41
% 7.75/1.49  lits eq                                 16
% 7.75/1.49  fd_pure                                 0
% 7.75/1.49  fd_pseudo                               0
% 7.75/1.49  fd_cond                                 0
% 7.75/1.49  fd_pseudo_cond                          0
% 7.75/1.49  AC symbols                              0
% 7.75/1.49  
% 7.75/1.49  ------ Input Options Time Limit: Unbounded
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  ------ 
% 7.75/1.49  Current options:
% 7.75/1.49  ------ 
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  ------ Proving...
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  % SZS status Theorem for theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  fof(f19,conjecture,(
% 7.75/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f20,negated_conjecture,(
% 7.75/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.49    inference(negated_conjecture,[],[f19])).
% 7.75/1.49  
% 7.75/1.49  fof(f32,plain,(
% 7.75/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.75/1.49    inference(ennf_transformation,[],[f20])).
% 7.75/1.49  
% 7.75/1.49  fof(f33,plain,(
% 7.75/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.49    inference(flattening,[],[f32])).
% 7.75/1.49  
% 7.75/1.49  fof(f34,plain,(
% 7.75/1.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.49    inference(nnf_transformation,[],[f33])).
% 7.75/1.49  
% 7.75/1.49  fof(f35,plain,(
% 7.75/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.49    inference(flattening,[],[f34])).
% 7.75/1.49  
% 7.75/1.49  fof(f37,plain,(
% 7.75/1.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.75/1.49    introduced(choice_axiom,[])).
% 7.75/1.49  
% 7.75/1.49  fof(f36,plain,(
% 7.75/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.75/1.49    introduced(choice_axiom,[])).
% 7.75/1.49  
% 7.75/1.49  fof(f38,plain,(
% 7.75/1.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.75/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 7.75/1.49  
% 7.75/1.49  fof(f60,plain,(
% 7.75/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.75/1.49    inference(cnf_transformation,[],[f38])).
% 7.75/1.49  
% 7.75/1.49  fof(f13,axiom,(
% 7.75/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f25,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.49    inference(ennf_transformation,[],[f13])).
% 7.75/1.49  
% 7.75/1.49  fof(f51,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f25])).
% 7.75/1.49  
% 7.75/1.49  fof(f61,plain,(
% 7.75/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.75/1.49    inference(cnf_transformation,[],[f38])).
% 7.75/1.49  
% 7.75/1.49  fof(f15,axiom,(
% 7.75/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f26,plain,(
% 7.75/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.49    inference(ennf_transformation,[],[f15])).
% 7.75/1.49  
% 7.75/1.49  fof(f27,plain,(
% 7.75/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.49    inference(flattening,[],[f26])).
% 7.75/1.49  
% 7.75/1.49  fof(f53,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f27])).
% 7.75/1.49  
% 7.75/1.49  fof(f59,plain,(
% 7.75/1.49    l1_pre_topc(sK0)),
% 7.75/1.49    inference(cnf_transformation,[],[f38])).
% 7.75/1.49  
% 7.75/1.49  fof(f5,axiom,(
% 7.75/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f43,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f5])).
% 7.75/1.49  
% 7.75/1.49  fof(f4,axiom,(
% 7.75/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f22,plain,(
% 7.75/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.75/1.49    inference(ennf_transformation,[],[f4])).
% 7.75/1.49  
% 7.75/1.49  fof(f42,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f22])).
% 7.75/1.49  
% 7.75/1.49  fof(f7,axiom,(
% 7.75/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f45,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f7])).
% 7.75/1.49  
% 7.75/1.49  fof(f66,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.75/1.49    inference(definition_unfolding,[],[f42,f45])).
% 7.75/1.49  
% 7.75/1.49  fof(f14,axiom,(
% 7.75/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f52,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f14])).
% 7.75/1.49  
% 7.75/1.49  fof(f70,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f52,f45])).
% 7.75/1.49  
% 7.75/1.49  fof(f2,axiom,(
% 7.75/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f40,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f2])).
% 7.75/1.49  
% 7.75/1.49  fof(f63,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f40,f45])).
% 7.75/1.49  
% 7.75/1.49  fof(f10,axiom,(
% 7.75/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f48,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f10])).
% 7.75/1.49  
% 7.75/1.49  fof(f11,axiom,(
% 7.75/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f49,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f11])).
% 7.75/1.49  
% 7.75/1.49  fof(f9,axiom,(
% 7.75/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f47,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f9])).
% 7.75/1.49  
% 7.75/1.49  fof(f68,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f49,f47])).
% 7.75/1.49  
% 7.75/1.49  fof(f3,axiom,(
% 7.75/1.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f41,plain,(
% 7.75/1.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.75/1.49    inference(cnf_transformation,[],[f3])).
% 7.75/1.49  
% 7.75/1.49  fof(f65,plain,(
% 7.75/1.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 7.75/1.49    inference(definition_unfolding,[],[f41,f47])).
% 7.75/1.49  
% 7.75/1.49  fof(f8,axiom,(
% 7.75/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f46,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f8])).
% 7.75/1.49  
% 7.75/1.49  fof(f67,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f46,f47])).
% 7.75/1.49  
% 7.75/1.49  fof(f6,axiom,(
% 7.75/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f44,plain,(
% 7.75/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.75/1.49    inference(cnf_transformation,[],[f6])).
% 7.75/1.49  
% 7.75/1.49  fof(f1,axiom,(
% 7.75/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f21,plain,(
% 7.75/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.75/1.49    inference(rectify,[],[f1])).
% 7.75/1.49  
% 7.75/1.49  fof(f39,plain,(
% 7.75/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.75/1.49    inference(cnf_transformation,[],[f21])).
% 7.75/1.49  
% 7.75/1.49  fof(f64,plain,(
% 7.75/1.49    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.75/1.49    inference(definition_unfolding,[],[f39,f45])).
% 7.75/1.49  
% 7.75/1.49  fof(f16,axiom,(
% 7.75/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f28,plain,(
% 7.75/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.75/1.49    inference(ennf_transformation,[],[f16])).
% 7.75/1.49  
% 7.75/1.49  fof(f29,plain,(
% 7.75/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.75/1.49    inference(flattening,[],[f28])).
% 7.75/1.49  
% 7.75/1.49  fof(f55,plain,(
% 7.75/1.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f29])).
% 7.75/1.49  
% 7.75/1.49  fof(f12,axiom,(
% 7.75/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f23,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.75/1.49    inference(ennf_transformation,[],[f12])).
% 7.75/1.49  
% 7.75/1.49  fof(f24,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.49    inference(flattening,[],[f23])).
% 7.75/1.49  
% 7.75/1.49  fof(f50,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f24])).
% 7.75/1.49  
% 7.75/1.49  fof(f69,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f50,f47])).
% 7.75/1.49  
% 7.75/1.49  fof(f18,axiom,(
% 7.75/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f31,plain,(
% 7.75/1.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.49    inference(ennf_transformation,[],[f18])).
% 7.75/1.49  
% 7.75/1.49  fof(f57,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f31])).
% 7.75/1.49  
% 7.75/1.49  fof(f17,axiom,(
% 7.75/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.75/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f30,plain,(
% 7.75/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.49    inference(ennf_transformation,[],[f17])).
% 7.75/1.49  
% 7.75/1.49  fof(f56,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f30])).
% 7.75/1.49  
% 7.75/1.49  fof(f54,plain,(
% 7.75/1.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f27])).
% 7.75/1.49  
% 7.75/1.49  fof(f62,plain,(
% 7.75/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.75/1.49    inference(cnf_transformation,[],[f38])).
% 7.75/1.49  
% 7.75/1.49  fof(f58,plain,(
% 7.75/1.49    v2_pre_topc(sK0)),
% 7.75/1.49    inference(cnf_transformation,[],[f38])).
% 7.75/1.49  
% 7.75/1.49  cnf(c_19,negated_conjecture,
% 7.75/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.75/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_630,plain,
% 7.75/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_10,plain,
% 7.75/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.75/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_638,plain,
% 7.75/1.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.75/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_12840,plain,
% 7.75/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_630,c_638]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_18,negated_conjecture,
% 7.75/1.49      ( v4_pre_topc(sK1,sK0)
% 7.75/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_631,plain,
% 7.75/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_13103,plain,
% 7.75/1.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_12840,c_631]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_13,plain,
% 7.75/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.49      | ~ l1_pre_topc(X1)
% 7.75/1.49      | k2_pre_topc(X1,X0) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_636,plain,
% 7.75/1.49      ( k2_pre_topc(X0,X1) = X1
% 7.75/1.49      | v4_pre_topc(X1,X0) != iProver_top
% 7.75/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_19971,plain,
% 7.75/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.49      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.75/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_630,c_636]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20,negated_conjecture,
% 7.75/1.49      ( l1_pre_topc(sK0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_23,plain,
% 7.75/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20268,plain,
% 7.75/1.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.75/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.49      inference(global_propositional_subsumption,
% 7.75/1.49                [status(thm)],
% 7.75/1.49                [c_19971,c_23]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20269,plain,
% 7.75/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.75/1.49      inference(renaming,[status(thm)],[c_20268]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20274,plain,
% 7.75/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_13103,c_20269]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_4,plain,
% 7.75/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_641,plain,
% 7.75/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_3,plain,
% 7.75/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_642,plain,
% 7.75/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.75/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_11,plain,
% 7.75/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_671,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.75/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_642,c_11]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_9723,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_641,c_671]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_0,plain,
% 7.75/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.75/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_668,plain,
% 7.75/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.75/1.49      inference(light_normalisation,[status(thm)],[c_0,c_11]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_13295,plain,
% 7.75/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_9723,c_668]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_7,plain,
% 7.75/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_8,plain,
% 7.75/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_2,plain,
% 7.75/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1191,plain,
% 7.75/1.49      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_8,c_2]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1373,plain,
% 7.75/1.49      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_7,c_1191]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_6,plain,
% 7.75/1.49      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.75/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_640,plain,
% 7.75/1.49      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_664,plain,
% 7.75/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_8,c_640]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1618,plain,
% 7.75/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_1373,c_664]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_9727,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_1618,c_671]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_5,plain,
% 7.75/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1205,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_5,c_11]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1842,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_7,c_1205]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_10542,plain,
% 7.75/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_9727,c_1842]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1,plain,
% 7.75/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1207,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_3143,plain,
% 7.75/1.49      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_1207,c_668]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_10599,plain,
% 7.75/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_10542,c_3143]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_13313,plain,
% 7.75/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_13295,c_10599]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14340,plain,
% 7.75/1.50      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_13313,c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3146,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_7,c_668]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10565,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_9727,c_3146]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10568,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_10565,c_5]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14342,plain,
% 7.75/1.50      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_14340,c_10568]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21381,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_20274,c_14342]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_635,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.75/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.75/1.50      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_639,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_700,plain,
% 7.75/1.50      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_639,c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19750,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_630,c_700]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20533,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_635,c_19750]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21128,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_20533,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21129,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_21128]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21137,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_630,c_21129]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_633,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1769,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_630,c_633]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_879,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2361,plain,
% 7.75/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1769,c_20,c_19,c_879]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21139,plain,
% 7.75/1.50      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_21137,c_2361]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21440,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_21381,c_21139]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_15,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_634,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19995,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_630,c_634]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_887,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20548,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_19995,c_20,c_19,c_887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23072,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_21440,c_20548]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12,plain,
% 7.75/1.50      ( v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) != X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_876,plain,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0)
% 7.75/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | ~ v2_pre_topc(sK0)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17,negated_conjecture,
% 7.75/1.50      ( ~ v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_23072,c_21440,c_876,c_17,c_19,c_20,c_21]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ Selected
% 7.75/1.50  
% 7.75/1.50  total_time:                             0.724
% 7.75/1.50  
%------------------------------------------------------------------------------
