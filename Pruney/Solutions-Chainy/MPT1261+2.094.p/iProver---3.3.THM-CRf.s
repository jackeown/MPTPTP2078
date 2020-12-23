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
% DateTime   : Thu Dec  3 12:14:38 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :  204 (2815 expanded)
%              Number of clauses        :  137 ( 892 expanded)
%              Number of leaves         :   20 ( 715 expanded)
%              Depth                    :   27
%              Number of atoms          :  451 (6443 expanded)
%              Number of equality atoms :  221 (3051 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f49,f49])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1308,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1309,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2321,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1309])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_159,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_201,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_160])).

cnf(c_1307,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_25266,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2321,c_1307])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1306,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1449,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1308,c_1306])).

cnf(c_25888,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_25266,c_1449])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26043,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_25888,c_11])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1317,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2,c_11])).

cnf(c_2028,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1317,c_11])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1312,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1861,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1312])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1313,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1319,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1313,c_1317])).

cnf(c_5562,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1861,c_1319])).

cnf(c_7274,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2028,c_5562])).

cnf(c_26909,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_26043,c_7274])).

cnf(c_26041,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_25888,c_1317])).

cnf(c_26967,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_26909,c_26041])).

cnf(c_42873,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_26967,c_7274])).

cnf(c_5560,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1312,c_1319])).

cnf(c_1792,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_11])).

cnf(c_5572,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5560,c_1792])).

cnf(c_7096,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5572,c_1317])).

cnf(c_7107,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7096,c_1317])).

cnf(c_25265,plain,
    ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1312,c_1307])).

cnf(c_25354,plain,
    ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_11,c_25265])).

cnf(c_25267,plain,
    ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1861,c_1307])).

cnf(c_25382,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2) ),
    inference(light_normalisation,[status(thm)],[c_25354,c_1317,c_25267])).

cnf(c_25503,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_25382,c_11])).

cnf(c_25705,plain,
    ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X0)))),X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)),X2)) ),
    inference(superposition,[status(thm)],[c_7107,c_25503])).

cnf(c_8247,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7107,c_2028])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1315,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2315,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1312,c_1315])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4181,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_2315,c_1])).

cnf(c_4304,plain,
    ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_4181])).

cnf(c_8237,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7107,c_4304])).

cnf(c_10401,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2028,c_8237])).

cnf(c_24072,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_8247,c_10401])).

cnf(c_24092,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_24072,c_10401])).

cnf(c_25859,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X2,X1)),X0)) ),
    inference(demodulation,[status(thm)],[c_25705,c_1317,c_8247,c_24092])).

cnf(c_42886,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))))) = k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_26967,c_25859])).

cnf(c_2027,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1317,c_11])).

cnf(c_5571,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5560,c_2027])).

cnf(c_5701,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5571,c_1317])).

cnf(c_5712,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_5701,c_1317])).

cnf(c_26896,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_26043,c_5712])).

cnf(c_26973,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_26896,c_26043])).

cnf(c_35986,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(superposition,[status(thm)],[c_25859,c_2028])).

cnf(c_41779,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_26041,c_35986])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_163,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_348,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_349,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_163,c_349])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_21])).

cnf(c_700,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_396])).

cnf(c_701,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_25887,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_25266,c_701])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1314,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3175,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1314])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_160])).

cnf(c_696,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_697,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_733,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_200,c_697])).

cnf(c_1303,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_4634,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1303])).

cnf(c_9587,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(X0,X1)) = k2_xboole_0(sK1,k4_xboole_0(X0,X1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_4634])).

cnf(c_9704,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2321,c_9587])).

cnf(c_9709,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_9704,c_4181])).

cnf(c_36747,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_25887,c_9709])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1305,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1410,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1308,c_1305])).

cnf(c_36771,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_36747,c_1410])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_321,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_322,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_163,c_322])).

cnf(c_405,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_407,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_21])).

cnf(c_19,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_161,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_284,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_285,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_22])).

cnf(c_290,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_290])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_421,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_21])).

cnf(c_698,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_421])).

cnf(c_699,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_698])).

cnf(c_735,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(bin_hyper_res,[status(thm)],[c_407,c_699])).

cnf(c_1302,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_36773,plain,
    ( sK1 != sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_36771,c_1302])).

cnf(c_36775,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_36773])).

cnf(c_39567,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_36775,c_1319])).

cnf(c_42137,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_41779,c_39567])).

cnf(c_42901,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) = k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_42886,c_26973,c_42137])).

cnf(c_42912,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_42873,c_42901])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1311,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1316,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1311,c_7])).

cnf(c_2322,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1309])).

cnf(c_5564,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2322,c_1319])).

cnf(c_8098,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5560,c_5712])).

cnf(c_8142,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8098,c_5560])).

cnf(c_42913,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_42912,c_5564,c_8142])).

cnf(c_25884,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_25266,c_699])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42913,c_36771,c_25884])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.54/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.54/1.99  
% 11.54/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.54/1.99  
% 11.54/1.99  ------  iProver source info
% 11.54/1.99  
% 11.54/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.54/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.54/1.99  git: non_committed_changes: false
% 11.54/1.99  git: last_make_outside_of_git: false
% 11.54/1.99  
% 11.54/1.99  ------ 
% 11.54/1.99  
% 11.54/1.99  ------ Input Options
% 11.54/1.99  
% 11.54/1.99  --out_options                           all
% 11.54/1.99  --tptp_safe_out                         true
% 11.54/1.99  --problem_path                          ""
% 11.54/1.99  --include_path                          ""
% 11.54/1.99  --clausifier                            res/vclausify_rel
% 11.54/1.99  --clausifier_options                    ""
% 11.54/1.99  --stdin                                 false
% 11.54/1.99  --stats_out                             all
% 11.54/1.99  
% 11.54/1.99  ------ General Options
% 11.54/1.99  
% 11.54/1.99  --fof                                   false
% 11.54/1.99  --time_out_real                         305.
% 11.54/1.99  --time_out_virtual                      -1.
% 11.54/1.99  --symbol_type_check                     false
% 11.54/1.99  --clausify_out                          false
% 11.54/1.99  --sig_cnt_out                           false
% 11.54/1.99  --trig_cnt_out                          false
% 11.54/1.99  --trig_cnt_out_tolerance                1.
% 11.54/1.99  --trig_cnt_out_sk_spl                   false
% 11.54/1.99  --abstr_cl_out                          false
% 11.54/1.99  
% 11.54/1.99  ------ Global Options
% 11.54/1.99  
% 11.54/1.99  --schedule                              default
% 11.54/1.99  --add_important_lit                     false
% 11.54/1.99  --prop_solver_per_cl                    1000
% 11.54/1.99  --min_unsat_core                        false
% 11.54/1.99  --soft_assumptions                      false
% 11.54/1.99  --soft_lemma_size                       3
% 11.54/1.99  --prop_impl_unit_size                   0
% 11.54/1.99  --prop_impl_unit                        []
% 11.54/1.99  --share_sel_clauses                     true
% 11.54/1.99  --reset_solvers                         false
% 11.54/1.99  --bc_imp_inh                            [conj_cone]
% 11.54/1.99  --conj_cone_tolerance                   3.
% 11.54/1.99  --extra_neg_conj                        none
% 11.54/1.99  --large_theory_mode                     true
% 11.54/1.99  --prolific_symb_bound                   200
% 11.54/1.99  --lt_threshold                          2000
% 11.54/1.99  --clause_weak_htbl                      true
% 11.54/1.99  --gc_record_bc_elim                     false
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing Options
% 11.54/1.99  
% 11.54/1.99  --preprocessing_flag                    true
% 11.54/1.99  --time_out_prep_mult                    0.1
% 11.54/1.99  --splitting_mode                        input
% 11.54/1.99  --splitting_grd                         true
% 11.54/1.99  --splitting_cvd                         false
% 11.54/1.99  --splitting_cvd_svl                     false
% 11.54/1.99  --splitting_nvd                         32
% 11.54/1.99  --sub_typing                            true
% 11.54/1.99  --prep_gs_sim                           true
% 11.54/1.99  --prep_unflatten                        true
% 11.54/1.99  --prep_res_sim                          true
% 11.54/1.99  --prep_upred                            true
% 11.54/1.99  --prep_sem_filter                       exhaustive
% 11.54/1.99  --prep_sem_filter_out                   false
% 11.54/1.99  --pred_elim                             true
% 11.54/1.99  --res_sim_input                         true
% 11.54/1.99  --eq_ax_congr_red                       true
% 11.54/1.99  --pure_diseq_elim                       true
% 11.54/1.99  --brand_transform                       false
% 11.54/1.99  --non_eq_to_eq                          false
% 11.54/1.99  --prep_def_merge                        true
% 11.54/1.99  --prep_def_merge_prop_impl              false
% 11.54/1.99  --prep_def_merge_mbd                    true
% 11.54/1.99  --prep_def_merge_tr_red                 false
% 11.54/1.99  --prep_def_merge_tr_cl                  false
% 11.54/1.99  --smt_preprocessing                     true
% 11.54/1.99  --smt_ac_axioms                         fast
% 11.54/1.99  --preprocessed_out                      false
% 11.54/1.99  --preprocessed_stats                    false
% 11.54/1.99  
% 11.54/1.99  ------ Abstraction refinement Options
% 11.54/1.99  
% 11.54/1.99  --abstr_ref                             []
% 11.54/1.99  --abstr_ref_prep                        false
% 11.54/1.99  --abstr_ref_until_sat                   false
% 11.54/1.99  --abstr_ref_sig_restrict                funpre
% 11.54/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.99  --abstr_ref_under                       []
% 11.54/1.99  
% 11.54/1.99  ------ SAT Options
% 11.54/1.99  
% 11.54/1.99  --sat_mode                              false
% 11.54/1.99  --sat_fm_restart_options                ""
% 11.54/1.99  --sat_gr_def                            false
% 11.54/1.99  --sat_epr_types                         true
% 11.54/1.99  --sat_non_cyclic_types                  false
% 11.54/1.99  --sat_finite_models                     false
% 11.54/1.99  --sat_fm_lemmas                         false
% 11.54/1.99  --sat_fm_prep                           false
% 11.54/1.99  --sat_fm_uc_incr                        true
% 11.54/1.99  --sat_out_model                         small
% 11.54/1.99  --sat_out_clauses                       false
% 11.54/1.99  
% 11.54/1.99  ------ QBF Options
% 11.54/1.99  
% 11.54/1.99  --qbf_mode                              false
% 11.54/1.99  --qbf_elim_univ                         false
% 11.54/1.99  --qbf_dom_inst                          none
% 11.54/1.99  --qbf_dom_pre_inst                      false
% 11.54/1.99  --qbf_sk_in                             false
% 11.54/1.99  --qbf_pred_elim                         true
% 11.54/1.99  --qbf_split                             512
% 11.54/1.99  
% 11.54/1.99  ------ BMC1 Options
% 11.54/1.99  
% 11.54/1.99  --bmc1_incremental                      false
% 11.54/1.99  --bmc1_axioms                           reachable_all
% 11.54/1.99  --bmc1_min_bound                        0
% 11.54/1.99  --bmc1_max_bound                        -1
% 11.54/1.99  --bmc1_max_bound_default                -1
% 11.54/1.99  --bmc1_symbol_reachability              true
% 11.54/1.99  --bmc1_property_lemmas                  false
% 11.54/1.99  --bmc1_k_induction                      false
% 11.54/1.99  --bmc1_non_equiv_states                 false
% 11.54/1.99  --bmc1_deadlock                         false
% 11.54/1.99  --bmc1_ucm                              false
% 11.54/1.99  --bmc1_add_unsat_core                   none
% 11.54/1.99  --bmc1_unsat_core_children              false
% 11.54/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.99  --bmc1_out_stat                         full
% 11.54/1.99  --bmc1_ground_init                      false
% 11.54/1.99  --bmc1_pre_inst_next_state              false
% 11.54/1.99  --bmc1_pre_inst_state                   false
% 11.54/1.99  --bmc1_pre_inst_reach_state             false
% 11.54/1.99  --bmc1_out_unsat_core                   false
% 11.54/1.99  --bmc1_aig_witness_out                  false
% 11.54/1.99  --bmc1_verbose                          false
% 11.54/1.99  --bmc1_dump_clauses_tptp                false
% 11.54/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.99  --bmc1_dump_file                        -
% 11.54/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.99  --bmc1_ucm_extend_mode                  1
% 11.54/1.99  --bmc1_ucm_init_mode                    2
% 11.54/1.99  --bmc1_ucm_cone_mode                    none
% 11.54/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.99  --bmc1_ucm_relax_model                  4
% 11.54/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.99  --bmc1_ucm_layered_model                none
% 11.54/1.99  --bmc1_ucm_max_lemma_size               10
% 11.54/1.99  
% 11.54/1.99  ------ AIG Options
% 11.54/1.99  
% 11.54/1.99  --aig_mode                              false
% 11.54/1.99  
% 11.54/1.99  ------ Instantiation Options
% 11.54/1.99  
% 11.54/1.99  --instantiation_flag                    true
% 11.54/1.99  --inst_sos_flag                         true
% 11.54/1.99  --inst_sos_phase                        true
% 11.54/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel_side                     num_symb
% 11.54/1.99  --inst_solver_per_active                1400
% 11.54/1.99  --inst_solver_calls_frac                1.
% 11.54/1.99  --inst_passive_queue_type               priority_queues
% 11.54/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.99  --inst_passive_queues_freq              [25;2]
% 11.54/1.99  --inst_dismatching                      true
% 11.54/1.99  --inst_eager_unprocessed_to_passive     true
% 11.54/1.99  --inst_prop_sim_given                   true
% 11.54/1.99  --inst_prop_sim_new                     false
% 11.54/1.99  --inst_subs_new                         false
% 11.54/1.99  --inst_eq_res_simp                      false
% 11.54/1.99  --inst_subs_given                       false
% 11.54/1.99  --inst_orphan_elimination               true
% 11.54/1.99  --inst_learning_loop_flag               true
% 11.54/1.99  --inst_learning_start                   3000
% 11.54/1.99  --inst_learning_factor                  2
% 11.54/1.99  --inst_start_prop_sim_after_learn       3
% 11.54/1.99  --inst_sel_renew                        solver
% 11.54/1.99  --inst_lit_activity_flag                true
% 11.54/1.99  --inst_restr_to_given                   false
% 11.54/1.99  --inst_activity_threshold               500
% 11.54/1.99  --inst_out_proof                        true
% 11.54/1.99  
% 11.54/1.99  ------ Resolution Options
% 11.54/1.99  
% 11.54/1.99  --resolution_flag                       true
% 11.54/1.99  --res_lit_sel                           adaptive
% 11.54/1.99  --res_lit_sel_side                      none
% 11.54/1.99  --res_ordering                          kbo
% 11.54/1.99  --res_to_prop_solver                    active
% 11.54/1.99  --res_prop_simpl_new                    false
% 11.54/1.99  --res_prop_simpl_given                  true
% 11.54/1.99  --res_passive_queue_type                priority_queues
% 11.54/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/1.99  --res_passive_queues_freq               [15;5]
% 11.54/1.99  --res_forward_subs                      full
% 11.54/1.99  --res_backward_subs                     full
% 11.54/1.99  --res_forward_subs_resolution           true
% 11.54/1.99  --res_backward_subs_resolution          true
% 11.54/1.99  --res_orphan_elimination                true
% 11.54/1.99  --res_time_limit                        2.
% 11.54/1.99  --res_out_proof                         true
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Options
% 11.54/1.99  
% 11.54/1.99  --superposition_flag                    true
% 11.54/1.99  --sup_passive_queue_type                priority_queues
% 11.54/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.54/1.99  --demod_completeness_check              fast
% 11.54/1.99  --demod_use_ground                      true
% 11.54/1.99  --sup_to_prop_solver                    passive
% 11.54/1.99  --sup_prop_simpl_new                    true
% 11.54/1.99  --sup_prop_simpl_given                  true
% 11.54/1.99  --sup_fun_splitting                     true
% 11.54/1.99  --sup_smt_interval                      50000
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Simplification Setup
% 11.54/1.99  
% 11.54/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.54/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.54/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.54/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.54/1.99  --sup_immed_triv                        [TrivRules]
% 11.54/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.99  --sup_immed_bw_main                     []
% 11.54/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.54/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.99  --sup_input_bw                          []
% 11.54/1.99  
% 11.54/1.99  ------ Combination Options
% 11.54/1.99  
% 11.54/1.99  --comb_res_mult                         3
% 11.54/1.99  --comb_sup_mult                         2
% 11.54/1.99  --comb_inst_mult                        10
% 11.54/1.99  
% 11.54/1.99  ------ Debug Options
% 11.54/1.99  
% 11.54/1.99  --dbg_backtrace                         false
% 11.54/1.99  --dbg_dump_prop_clauses                 false
% 11.54/1.99  --dbg_dump_prop_clauses_file            -
% 11.54/1.99  --dbg_out_stat                          false
% 11.54/1.99  ------ Parsing...
% 11.54/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.54/1.99  ------ Proving...
% 11.54/1.99  ------ Problem Properties 
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  clauses                                 21
% 11.54/1.99  conjectures                             1
% 11.54/1.99  EPR                                     1
% 11.54/1.99  Horn                                    20
% 11.54/1.99  unary                                   8
% 11.54/1.99  binary                                  10
% 11.54/1.99  lits                                    37
% 11.54/1.99  lits eq                                 17
% 11.54/1.99  fd_pure                                 0
% 11.54/1.99  fd_pseudo                               0
% 11.54/1.99  fd_cond                                 0
% 11.54/1.99  fd_pseudo_cond                          0
% 11.54/1.99  AC symbols                              0
% 11.54/1.99  
% 11.54/1.99  ------ Schedule dynamic 5 is on 
% 11.54/1.99  
% 11.54/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  ------ 
% 11.54/1.99  Current options:
% 11.54/1.99  ------ 
% 11.54/1.99  
% 11.54/1.99  ------ Input Options
% 11.54/1.99  
% 11.54/1.99  --out_options                           all
% 11.54/1.99  --tptp_safe_out                         true
% 11.54/1.99  --problem_path                          ""
% 11.54/1.99  --include_path                          ""
% 11.54/1.99  --clausifier                            res/vclausify_rel
% 11.54/1.99  --clausifier_options                    ""
% 11.54/1.99  --stdin                                 false
% 11.54/1.99  --stats_out                             all
% 11.54/1.99  
% 11.54/1.99  ------ General Options
% 11.54/1.99  
% 11.54/1.99  --fof                                   false
% 11.54/1.99  --time_out_real                         305.
% 11.54/1.99  --time_out_virtual                      -1.
% 11.54/1.99  --symbol_type_check                     false
% 11.54/1.99  --clausify_out                          false
% 11.54/1.99  --sig_cnt_out                           false
% 11.54/1.99  --trig_cnt_out                          false
% 11.54/1.99  --trig_cnt_out_tolerance                1.
% 11.54/1.99  --trig_cnt_out_sk_spl                   false
% 11.54/1.99  --abstr_cl_out                          false
% 11.54/1.99  
% 11.54/1.99  ------ Global Options
% 11.54/1.99  
% 11.54/1.99  --schedule                              default
% 11.54/1.99  --add_important_lit                     false
% 11.54/1.99  --prop_solver_per_cl                    1000
% 11.54/1.99  --min_unsat_core                        false
% 11.54/1.99  --soft_assumptions                      false
% 11.54/1.99  --soft_lemma_size                       3
% 11.54/1.99  --prop_impl_unit_size                   0
% 11.54/1.99  --prop_impl_unit                        []
% 11.54/1.99  --share_sel_clauses                     true
% 11.54/1.99  --reset_solvers                         false
% 11.54/1.99  --bc_imp_inh                            [conj_cone]
% 11.54/1.99  --conj_cone_tolerance                   3.
% 11.54/1.99  --extra_neg_conj                        none
% 11.54/1.99  --large_theory_mode                     true
% 11.54/1.99  --prolific_symb_bound                   200
% 11.54/1.99  --lt_threshold                          2000
% 11.54/1.99  --clause_weak_htbl                      true
% 11.54/1.99  --gc_record_bc_elim                     false
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing Options
% 11.54/1.99  
% 11.54/1.99  --preprocessing_flag                    true
% 11.54/1.99  --time_out_prep_mult                    0.1
% 11.54/1.99  --splitting_mode                        input
% 11.54/1.99  --splitting_grd                         true
% 11.54/1.99  --splitting_cvd                         false
% 11.54/1.99  --splitting_cvd_svl                     false
% 11.54/1.99  --splitting_nvd                         32
% 11.54/1.99  --sub_typing                            true
% 11.54/1.99  --prep_gs_sim                           true
% 11.54/1.99  --prep_unflatten                        true
% 11.54/1.99  --prep_res_sim                          true
% 11.54/1.99  --prep_upred                            true
% 11.54/1.99  --prep_sem_filter                       exhaustive
% 11.54/1.99  --prep_sem_filter_out                   false
% 11.54/1.99  --pred_elim                             true
% 11.54/1.99  --res_sim_input                         true
% 11.54/1.99  --eq_ax_congr_red                       true
% 11.54/1.99  --pure_diseq_elim                       true
% 11.54/1.99  --brand_transform                       false
% 11.54/1.99  --non_eq_to_eq                          false
% 11.54/1.99  --prep_def_merge                        true
% 11.54/1.99  --prep_def_merge_prop_impl              false
% 11.54/1.99  --prep_def_merge_mbd                    true
% 11.54/1.99  --prep_def_merge_tr_red                 false
% 11.54/1.99  --prep_def_merge_tr_cl                  false
% 11.54/1.99  --smt_preprocessing                     true
% 11.54/1.99  --smt_ac_axioms                         fast
% 11.54/1.99  --preprocessed_out                      false
% 11.54/1.99  --preprocessed_stats                    false
% 11.54/1.99  
% 11.54/1.99  ------ Abstraction refinement Options
% 11.54/1.99  
% 11.54/1.99  --abstr_ref                             []
% 11.54/1.99  --abstr_ref_prep                        false
% 11.54/1.99  --abstr_ref_until_sat                   false
% 11.54/1.99  --abstr_ref_sig_restrict                funpre
% 11.54/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.99  --abstr_ref_under                       []
% 11.54/1.99  
% 11.54/1.99  ------ SAT Options
% 11.54/1.99  
% 11.54/1.99  --sat_mode                              false
% 11.54/1.99  --sat_fm_restart_options                ""
% 11.54/1.99  --sat_gr_def                            false
% 11.54/1.99  --sat_epr_types                         true
% 11.54/1.99  --sat_non_cyclic_types                  false
% 11.54/1.99  --sat_finite_models                     false
% 11.54/1.99  --sat_fm_lemmas                         false
% 11.54/1.99  --sat_fm_prep                           false
% 11.54/1.99  --sat_fm_uc_incr                        true
% 11.54/1.99  --sat_out_model                         small
% 11.54/1.99  --sat_out_clauses                       false
% 11.54/1.99  
% 11.54/1.99  ------ QBF Options
% 11.54/1.99  
% 11.54/1.99  --qbf_mode                              false
% 11.54/1.99  --qbf_elim_univ                         false
% 11.54/1.99  --qbf_dom_inst                          none
% 11.54/1.99  --qbf_dom_pre_inst                      false
% 11.54/1.99  --qbf_sk_in                             false
% 11.54/1.99  --qbf_pred_elim                         true
% 11.54/1.99  --qbf_split                             512
% 11.54/1.99  
% 11.54/1.99  ------ BMC1 Options
% 11.54/1.99  
% 11.54/1.99  --bmc1_incremental                      false
% 11.54/1.99  --bmc1_axioms                           reachable_all
% 11.54/1.99  --bmc1_min_bound                        0
% 11.54/1.99  --bmc1_max_bound                        -1
% 11.54/1.99  --bmc1_max_bound_default                -1
% 11.54/1.99  --bmc1_symbol_reachability              true
% 11.54/1.99  --bmc1_property_lemmas                  false
% 11.54/1.99  --bmc1_k_induction                      false
% 11.54/1.99  --bmc1_non_equiv_states                 false
% 11.54/1.99  --bmc1_deadlock                         false
% 11.54/1.99  --bmc1_ucm                              false
% 11.54/1.99  --bmc1_add_unsat_core                   none
% 11.54/1.99  --bmc1_unsat_core_children              false
% 11.54/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.99  --bmc1_out_stat                         full
% 11.54/1.99  --bmc1_ground_init                      false
% 11.54/1.99  --bmc1_pre_inst_next_state              false
% 11.54/1.99  --bmc1_pre_inst_state                   false
% 11.54/1.99  --bmc1_pre_inst_reach_state             false
% 11.54/1.99  --bmc1_out_unsat_core                   false
% 11.54/1.99  --bmc1_aig_witness_out                  false
% 11.54/1.99  --bmc1_verbose                          false
% 11.54/1.99  --bmc1_dump_clauses_tptp                false
% 11.54/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.99  --bmc1_dump_file                        -
% 11.54/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.99  --bmc1_ucm_extend_mode                  1
% 11.54/1.99  --bmc1_ucm_init_mode                    2
% 11.54/1.99  --bmc1_ucm_cone_mode                    none
% 11.54/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.99  --bmc1_ucm_relax_model                  4
% 11.54/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.99  --bmc1_ucm_layered_model                none
% 11.54/1.99  --bmc1_ucm_max_lemma_size               10
% 11.54/1.99  
% 11.54/1.99  ------ AIG Options
% 11.54/1.99  
% 11.54/1.99  --aig_mode                              false
% 11.54/1.99  
% 11.54/1.99  ------ Instantiation Options
% 11.54/1.99  
% 11.54/1.99  --instantiation_flag                    true
% 11.54/1.99  --inst_sos_flag                         true
% 11.54/1.99  --inst_sos_phase                        true
% 11.54/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel_side                     none
% 11.54/1.99  --inst_solver_per_active                1400
% 11.54/1.99  --inst_solver_calls_frac                1.
% 11.54/1.99  --inst_passive_queue_type               priority_queues
% 11.54/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.99  --inst_passive_queues_freq              [25;2]
% 11.54/1.99  --inst_dismatching                      true
% 11.54/1.99  --inst_eager_unprocessed_to_passive     true
% 11.54/2.00  --inst_prop_sim_given                   true
% 11.54/2.00  --inst_prop_sim_new                     false
% 11.54/2.00  --inst_subs_new                         false
% 11.54/2.00  --inst_eq_res_simp                      false
% 11.54/2.00  --inst_subs_given                       false
% 11.54/2.00  --inst_orphan_elimination               true
% 11.54/2.00  --inst_learning_loop_flag               true
% 11.54/2.00  --inst_learning_start                   3000
% 11.54/2.00  --inst_learning_factor                  2
% 11.54/2.00  --inst_start_prop_sim_after_learn       3
% 11.54/2.00  --inst_sel_renew                        solver
% 11.54/2.00  --inst_lit_activity_flag                true
% 11.54/2.00  --inst_restr_to_given                   false
% 11.54/2.00  --inst_activity_threshold               500
% 11.54/2.00  --inst_out_proof                        true
% 11.54/2.00  
% 11.54/2.00  ------ Resolution Options
% 11.54/2.00  
% 11.54/2.00  --resolution_flag                       false
% 11.54/2.00  --res_lit_sel                           adaptive
% 11.54/2.00  --res_lit_sel_side                      none
% 11.54/2.00  --res_ordering                          kbo
% 11.54/2.00  --res_to_prop_solver                    active
% 11.54/2.00  --res_prop_simpl_new                    false
% 11.54/2.00  --res_prop_simpl_given                  true
% 11.54/2.00  --res_passive_queue_type                priority_queues
% 11.54/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/2.00  --res_passive_queues_freq               [15;5]
% 11.54/2.00  --res_forward_subs                      full
% 11.54/2.00  --res_backward_subs                     full
% 11.54/2.00  --res_forward_subs_resolution           true
% 11.54/2.00  --res_backward_subs_resolution          true
% 11.54/2.00  --res_orphan_elimination                true
% 11.54/2.00  --res_time_limit                        2.
% 11.54/2.00  --res_out_proof                         true
% 11.54/2.00  
% 11.54/2.00  ------ Superposition Options
% 11.54/2.00  
% 11.54/2.00  --superposition_flag                    true
% 11.54/2.00  --sup_passive_queue_type                priority_queues
% 11.54/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.54/2.00  --demod_completeness_check              fast
% 11.54/2.00  --demod_use_ground                      true
% 11.54/2.00  --sup_to_prop_solver                    passive
% 11.54/2.00  --sup_prop_simpl_new                    true
% 11.54/2.00  --sup_prop_simpl_given                  true
% 11.54/2.00  --sup_fun_splitting                     true
% 11.54/2.00  --sup_smt_interval                      50000
% 11.54/2.00  
% 11.54/2.00  ------ Superposition Simplification Setup
% 11.54/2.00  
% 11.54/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.54/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.54/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.54/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.54/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.54/2.00  --sup_immed_triv                        [TrivRules]
% 11.54/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/2.00  --sup_immed_bw_main                     []
% 11.54/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.54/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/2.00  --sup_input_bw                          []
% 11.54/2.00  
% 11.54/2.00  ------ Combination Options
% 11.54/2.00  
% 11.54/2.00  --comb_res_mult                         3
% 11.54/2.00  --comb_sup_mult                         2
% 11.54/2.00  --comb_inst_mult                        10
% 11.54/2.00  
% 11.54/2.00  ------ Debug Options
% 11.54/2.00  
% 11.54/2.00  --dbg_backtrace                         false
% 11.54/2.00  --dbg_dump_prop_clauses                 false
% 11.54/2.00  --dbg_dump_prop_clauses_file            -
% 11.54/2.00  --dbg_out_stat                          false
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  ------ Proving...
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  % SZS status Theorem for theBenchmark.p
% 11.54/2.00  
% 11.54/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.54/2.00  
% 11.54/2.00  fof(f19,conjecture,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f20,negated_conjecture,(
% 11.54/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.54/2.00    inference(negated_conjecture,[],[f19])).
% 11.54/2.00  
% 11.54/2.00  fof(f34,plain,(
% 11.54/2.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f20])).
% 11.54/2.00  
% 11.54/2.00  fof(f35,plain,(
% 11.54/2.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.54/2.00    inference(flattening,[],[f34])).
% 11.54/2.00  
% 11.54/2.00  fof(f37,plain,(
% 11.54/2.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.54/2.00    inference(nnf_transformation,[],[f35])).
% 11.54/2.00  
% 11.54/2.00  fof(f38,plain,(
% 11.54/2.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.54/2.00    inference(flattening,[],[f37])).
% 11.54/2.00  
% 11.54/2.00  fof(f40,plain,(
% 11.54/2.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f39,plain,(
% 11.54/2.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f41,plain,(
% 11.54/2.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.54/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 11.54/2.00  
% 11.54/2.00  fof(f64,plain,(
% 11.54/2.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f14,axiom,(
% 11.54/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f36,plain,(
% 11.54/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.54/2.00    inference(nnf_transformation,[],[f14])).
% 11.54/2.00  
% 11.54/2.00  fof(f55,plain,(
% 11.54/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f36])).
% 11.54/2.00  
% 11.54/2.00  fof(f12,axiom,(
% 11.54/2.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f27,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f12])).
% 11.54/2.00  
% 11.54/2.00  fof(f53,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f27])).
% 11.54/2.00  
% 11.54/2.00  fof(f56,plain,(
% 11.54/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f36])).
% 11.54/2.00  
% 11.54/2.00  fof(f18,axiom,(
% 11.54/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f33,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(ennf_transformation,[],[f18])).
% 11.54/2.00  
% 11.54/2.00  fof(f61,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f33])).
% 11.54/2.00  
% 11.54/2.00  fof(f63,plain,(
% 11.54/2.00    l1_pre_topc(sK0)),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f13,axiom,(
% 11.54/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f54,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f13])).
% 11.54/2.00  
% 11.54/2.00  fof(f8,axiom,(
% 11.54/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f49,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f8])).
% 11.54/2.00  
% 11.54/2.00  fof(f70,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.54/2.00    inference(definition_unfolding,[],[f54,f49])).
% 11.54/2.00  
% 11.54/2.00  fof(f2,axiom,(
% 11.54/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f43,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f2])).
% 11.54/2.00  
% 11.54/2.00  fof(f68,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.54/2.00    inference(definition_unfolding,[],[f43,f49,f49])).
% 11.54/2.00  
% 11.54/2.00  fof(f7,axiom,(
% 11.54/2.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f48,plain,(
% 11.54/2.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f7])).
% 11.54/2.00  
% 11.54/2.00  fof(f6,axiom,(
% 11.54/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f24,plain,(
% 11.54/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.54/2.00    inference(ennf_transformation,[],[f6])).
% 11.54/2.00  
% 11.54/2.00  fof(f47,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f24])).
% 11.54/2.00  
% 11.54/2.00  fof(f69,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(definition_unfolding,[],[f47,f49])).
% 11.54/2.00  
% 11.54/2.00  fof(f4,axiom,(
% 11.54/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f21,plain,(
% 11.54/2.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.54/2.00    inference(ennf_transformation,[],[f4])).
% 11.54/2.00  
% 11.54/2.00  fof(f45,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f21])).
% 11.54/2.00  
% 11.54/2.00  fof(f1,axiom,(
% 11.54/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f42,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f1])).
% 11.54/2.00  
% 11.54/2.00  fof(f65,plain,(
% 11.54/2.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f15,axiom,(
% 11.54/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f28,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(ennf_transformation,[],[f15])).
% 11.54/2.00  
% 11.54/2.00  fof(f29,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(flattening,[],[f28])).
% 11.54/2.00  
% 11.54/2.00  fof(f57,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f29])).
% 11.54/2.00  
% 11.54/2.00  fof(f5,axiom,(
% 11.54/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f22,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.54/2.00    inference(ennf_transformation,[],[f5])).
% 11.54/2.00  
% 11.54/2.00  fof(f23,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.54/2.00    inference(flattening,[],[f22])).
% 11.54/2.00  
% 11.54/2.00  fof(f46,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f23])).
% 11.54/2.00  
% 11.54/2.00  fof(f11,axiom,(
% 11.54/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f25,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.54/2.00    inference(ennf_transformation,[],[f11])).
% 11.54/2.00  
% 11.54/2.00  fof(f26,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.54/2.00    inference(flattening,[],[f25])).
% 11.54/2.00  
% 11.54/2.00  fof(f52,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f26])).
% 11.54/2.00  
% 11.54/2.00  fof(f16,axiom,(
% 11.54/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f30,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(ennf_transformation,[],[f16])).
% 11.54/2.00  
% 11.54/2.00  fof(f59,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f30])).
% 11.54/2.00  
% 11.54/2.00  fof(f17,axiom,(
% 11.54/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f31,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(ennf_transformation,[],[f17])).
% 11.54/2.00  
% 11.54/2.00  fof(f32,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(flattening,[],[f31])).
% 11.54/2.00  
% 11.54/2.00  fof(f60,plain,(
% 11.54/2.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f32])).
% 11.54/2.00  
% 11.54/2.00  fof(f66,plain,(
% 11.54/2.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f58,plain,(
% 11.54/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f29])).
% 11.54/2.00  
% 11.54/2.00  fof(f62,plain,(
% 11.54/2.00    v2_pre_topc(sK0)),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f10,axiom,(
% 11.54/2.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f51,plain,(
% 11.54/2.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f10])).
% 11.54/2.00  
% 11.54/2.00  fof(f9,axiom,(
% 11.54/2.00    ! [X0] : k2_subset_1(X0) = X0),
% 11.54/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f50,plain,(
% 11.54/2.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.54/2.00    inference(cnf_transformation,[],[f9])).
% 11.54/2.00  
% 11.54/2.00  cnf(c_21,negated_conjecture,
% 11.54/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.54/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1308,plain,
% 11.54/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_13,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1309,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.54/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2321,plain,
% 11.54/2.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1308,c_1309]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_10,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.54/2.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.54/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_12,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_159,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_160,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_159]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_201,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.54/2.00      inference(bin_hyper_res,[status(thm)],[c_10,c_160]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1307,plain,
% 11.54/2.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.54/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25266,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2321,c_1307]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_18,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_22,negated_conjecture,
% 11.54/2.00      ( l1_pre_topc(sK0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_309,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 11.54/2.00      | sK0 != X1 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_310,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_309]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1306,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 11.54/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1449,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1308,c_1306]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25888,plain,
% 11.54/2.00      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25266,c_1449]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26043,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25888,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.54/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1317,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_2,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2028,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1317,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6,plain,
% 11.54/2.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1312,plain,
% 11.54/2.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1861,plain,
% 11.54/2.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11,c_1312]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1313,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.54/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1319,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X1
% 11.54/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_1313,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5562,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1861,c_1319]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7274,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2028,c_5562]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26909,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_26043,c_7274]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26041,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25888,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26967,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_26909,c_26041]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42873,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_26967,c_7274]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5560,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1312,c_1319]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1792,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5572,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_5560,c_1792]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7096,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_5572,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7107,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_7096,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25265,plain,
% 11.54/2.00      ( k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1312,c_1307]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25354,plain,
% 11.54/2.00      ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11,c_25265]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25267,plain,
% 11.54/2.00      ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1861,c_1307]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25382,plain,
% 11.54/2.00      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) = k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2) ),
% 11.54/2.00      inference(light_normalisation,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_25354,c_1317,c_25267]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25503,plain,
% 11.54/2.00      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25382,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25705,plain,
% 11.54/2.00      ( k4_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X0)))),X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)),X2)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_7107,c_25503]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8247,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_7107,c_2028]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.54/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1315,plain,
% 11.54/2.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2315,plain,
% 11.54/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1312,c_1315]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1,plain,
% 11.54/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4181,plain,
% 11.54/2.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2315,c_1]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4304,plain,
% 11.54/2.00      ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11,c_4181]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8237,plain,
% 11.54/2.00      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_7107,c_4304]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_10401,plain,
% 11.54/2.00      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2028,c_8237]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_24072,plain,
% 11.54/2.00      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_8247,c_10401]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_24092,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_24072,c_10401]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25859,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X2,X1)),X0)) ),
% 11.54/2.00      inference(demodulation,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_25705,c_1317,c_8247,c_24092]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42886,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))))) = k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_26967,c_25859]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2027,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1317,c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5571,plain,
% 11.54/2.00      ( k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_5560,c_2027]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5701,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_5571,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5712,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_5701,c_1317]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26896,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_26043,c_5712]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26973,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_26896,c_26043]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_35986,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X2,X1)))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25859,c_2028]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_41779,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_26041,c_35986]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_20,negated_conjecture,
% 11.54/2.00      ( v4_pre_topc(sK1,sK0)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_163,plain,
% 11.54/2.00      ( v4_pre_topc(sK1,sK0)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_20]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_15,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k2_pre_topc(X1,X0) = X0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_348,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | k2_pre_topc(X1,X0) = X0
% 11.54/2.00      | sK0 != X1 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_349,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,sK0)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k2_pre_topc(sK0,X0) = X0 ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_348]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_393,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,X0) = X0
% 11.54/2.00      | sK1 != X0
% 11.54/2.00      | sK0 != sK0 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_163,c_349]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_394,plain,
% 11.54/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_393]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_396,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_394,c_21]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_700,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_396]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_701,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_700]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25887,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.54/2.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25266,c_701]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.54/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1314,plain,
% 11.54/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.54/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.54/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3175,plain,
% 11.54/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.54/2.00      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1312,c_1314]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_9,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.54/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.54/2.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_200,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.54/2.00      | ~ r1_tarski(X2,X1)
% 11.54/2.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.54/2.00      inference(bin_hyper_res,[status(thm)],[c_9,c_160]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_696,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_697,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_696]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_733,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1)
% 11.54/2.00      | ~ r1_tarski(X2,X1)
% 11.54/2.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.54/2.00      inference(bin_hyper_res,[status(thm)],[c_200,c_697]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1303,plain,
% 11.54/2.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.54/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.54/2.00      | r1_tarski(X2,X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4634,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.54/2.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2321,c_1303]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_9587,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(X0,X1)) = k2_xboole_0(sK1,k4_xboole_0(X0,X1))
% 11.54/2.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_3175,c_4634]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_9704,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2321,c_9587]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_9709,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0)) = sK1 ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_9704,c_4181]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36747,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = sK1
% 11.54/2.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_25887,c_9709]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_16,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_336,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 11.54/2.00      | sK0 != X1 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_337,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_336]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1305,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 11.54/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1410,plain,
% 11.54/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1308,c_1305]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36771,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_36747,c_1410]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_17,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 11.54/2.00      | ~ l1_pre_topc(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_321,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 11.54/2.00      | sK0 != X1 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_322,plain,
% 11.54/2.00      ( ~ v4_pre_topc(X0,sK0)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | r1_tarski(k2_tops_1(sK0,X0),X0) ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_321]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_404,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | r1_tarski(k2_tops_1(sK0,X0),X0)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.54/2.00      | sK1 != X0
% 11.54/2.00      | sK0 != sK0 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_163,c_322]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_405,plain,
% 11.54/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_404]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_407,plain,
% 11.54/2.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_405,c_21]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_19,negated_conjecture,
% 11.54/2.00      ( ~ v4_pre_topc(sK1,sK0)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_161,plain,
% 11.54/2.00      ( ~ v4_pre_topc(sK1,sK0)
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_14,plain,
% 11.54/2.00      ( v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | ~ v2_pre_topc(X1)
% 11.54/2.00      | k2_pre_topc(X1,X0) != X0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_23,negated_conjecture,
% 11.54/2.00      ( v2_pre_topc(sK0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_284,plain,
% 11.54/2.00      ( v4_pre_topc(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k2_pre_topc(X1,X0) != X0
% 11.54/2.00      | sK0 != X1 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_285,plain,
% 11.54/2.00      ( v4_pre_topc(X0,sK0)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | ~ l1_pre_topc(sK0)
% 11.54/2.00      | k2_pre_topc(sK0,X0) != X0 ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_284]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_289,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | v4_pre_topc(X0,sK0)
% 11.54/2.00      | k2_pre_topc(sK0,X0) != X0 ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_285,c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_290,plain,
% 11.54/2.00      ( v4_pre_topc(X0,sK0)
% 11.54/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k2_pre_topc(sK0,X0) != X0 ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_289]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_418,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,X0) != X0
% 11.54/2.00      | sK1 != X0
% 11.54/2.00      | sK0 != sK0 ),
% 11.54/2.00      inference(resolution_lifted,[status(thm)],[c_161,c_290]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_419,plain,
% 11.54/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.54/2.00      inference(unflattening,[status(thm)],[c_418]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_421,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_419,c_21]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_698,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) != sK1
% 11.54/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(prop_impl,[status(thm)],[c_421]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_699,plain,
% 11.54/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.54/2.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_698]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_735,plain,
% 11.54/2.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.54/2.00      inference(bin_hyper_res,[status(thm)],[c_407,c_699]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1302,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) != sK1
% 11.54/2.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36773,plain,
% 11.54/2.00      ( sK1 != sK1 | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_36771,c_1302]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36775,plain,
% 11.54/2.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.54/2.00      inference(equality_resolution_simp,[status(thm)],[c_36773]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_39567,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_36775,c_1319]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42137,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))) ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_41779,c_39567]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42901,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) = k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))) ),
% 11.54/2.00      inference(light_normalisation,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_42886,c_26973,c_42137]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42912,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_42873,c_42901]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8,plain,
% 11.54/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.54/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1311,plain,
% 11.54/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7,plain,
% 11.54/2.00      ( k2_subset_1(X0) = X0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1316,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_1311,c_7]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2322,plain,
% 11.54/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1316,c_1309]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5564,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2322,c_1319]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8098,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_5560,c_5712]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8142,plain,
% 11.54/2.00      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.54/2.00      inference(light_normalisation,[status(thm)],[c_8098,c_5560]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42913,plain,
% 11.54/2.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_42912,c_5564,c_8142]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25884,plain,
% 11.54/2.00      ( k2_pre_topc(sK0,sK1) != sK1
% 11.54/2.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.54/2.00      inference(demodulation,[status(thm)],[c_25266,c_699]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(contradiction,plain,
% 11.54/2.00      ( $false ),
% 11.54/2.00      inference(minisat,[status(thm)],[c_42913,c_36771,c_25884]) ).
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.54/2.00  
% 11.54/2.00  ------                               Statistics
% 11.54/2.00  
% 11.54/2.00  ------ General
% 11.54/2.00  
% 11.54/2.00  abstr_ref_over_cycles:                  0
% 11.54/2.00  abstr_ref_under_cycles:                 0
% 11.54/2.00  gc_basic_clause_elim:                   0
% 11.54/2.00  forced_gc_time:                         0
% 11.54/2.00  parsing_time:                           0.009
% 11.54/2.00  unif_index_cands_time:                  0.
% 11.54/2.00  unif_index_add_time:                    0.
% 11.54/2.00  orderings_time:                         0.
% 11.54/2.00  out_proof_time:                         0.013
% 11.54/2.00  total_time:                             1.132
% 11.54/2.00  num_of_symbols:                         51
% 11.54/2.00  num_of_terms:                           38265
% 11.54/2.00  
% 11.54/2.00  ------ Preprocessing
% 11.54/2.00  
% 11.54/2.00  num_of_splits:                          0
% 11.54/2.00  num_of_split_atoms:                     0
% 11.54/2.00  num_of_reused_defs:                     0
% 11.54/2.00  num_eq_ax_congr_red:                    27
% 11.54/2.00  num_of_sem_filtered_clauses:            1
% 11.54/2.00  num_of_subtypes:                        0
% 11.54/2.00  monotx_restored_types:                  0
% 11.54/2.00  sat_num_of_epr_types:                   0
% 11.54/2.00  sat_num_of_non_cyclic_types:            0
% 11.54/2.00  sat_guarded_non_collapsed_types:        0
% 11.54/2.00  num_pure_diseq_elim:                    0
% 11.54/2.00  simp_replaced_by:                       0
% 11.54/2.00  res_preprocessed:                       116
% 11.54/2.00  prep_upred:                             0
% 11.54/2.00  prep_unflattend:                        32
% 11.54/2.00  smt_new_axioms:                         0
% 11.54/2.00  pred_elim_cands:                        2
% 11.54/2.00  pred_elim:                              3
% 11.54/2.00  pred_elim_cl:                           3
% 11.54/2.00  pred_elim_cycles:                       5
% 11.54/2.00  merged_defs:                            16
% 11.54/2.00  merged_defs_ncl:                        0
% 11.54/2.00  bin_hyper_res:                          20
% 11.54/2.00  prep_cycles:                            4
% 11.54/2.00  pred_elim_time:                         0.006
% 11.54/2.00  splitting_time:                         0.
% 11.54/2.00  sem_filter_time:                        0.
% 11.54/2.00  monotx_time:                            0.
% 11.54/2.00  subtype_inf_time:                       0.
% 11.54/2.00  
% 11.54/2.00  ------ Problem properties
% 11.54/2.00  
% 11.54/2.00  clauses:                                21
% 11.54/2.00  conjectures:                            1
% 11.54/2.00  epr:                                    1
% 11.54/2.00  horn:                                   20
% 11.54/2.00  ground:                                 4
% 11.54/2.00  unary:                                  8
% 11.54/2.00  binary:                                 10
% 11.54/2.00  lits:                                   37
% 11.54/2.00  lits_eq:                                17
% 11.54/2.00  fd_pure:                                0
% 11.54/2.00  fd_pseudo:                              0
% 11.54/2.00  fd_cond:                                0
% 11.54/2.00  fd_pseudo_cond:                         0
% 11.54/2.00  ac_symbols:                             0
% 11.54/2.00  
% 11.54/2.00  ------ Propositional Solver
% 11.54/2.00  
% 11.54/2.00  prop_solver_calls:                      33
% 11.54/2.00  prop_fast_solver_calls:                 1000
% 11.54/2.00  smt_solver_calls:                       0
% 11.54/2.00  smt_fast_solver_calls:                  0
% 11.54/2.00  prop_num_of_clauses:                    16308
% 11.54/2.00  prop_preprocess_simplified:             36236
% 11.54/2.00  prop_fo_subsumed:                       6
% 11.54/2.00  prop_solver_time:                       0.
% 11.54/2.00  smt_solver_time:                        0.
% 11.54/2.00  smt_fast_solver_time:                   0.
% 11.54/2.00  prop_fast_solver_time:                  0.
% 11.54/2.00  prop_unsat_core_time:                   0.002
% 11.54/2.00  
% 11.54/2.00  ------ QBF
% 11.54/2.00  
% 11.54/2.00  qbf_q_res:                              0
% 11.54/2.00  qbf_num_tautologies:                    0
% 11.54/2.00  qbf_prep_cycles:                        0
% 11.54/2.00  
% 11.54/2.00  ------ BMC1
% 11.54/2.00  
% 11.54/2.00  bmc1_current_bound:                     -1
% 11.54/2.00  bmc1_last_solved_bound:                 -1
% 11.54/2.00  bmc1_unsat_core_size:                   -1
% 11.54/2.00  bmc1_unsat_core_parents_size:           -1
% 11.54/2.00  bmc1_merge_next_fun:                    0
% 11.54/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.54/2.00  
% 11.54/2.00  ------ Instantiation
% 11.54/2.00  
% 11.54/2.00  inst_num_of_clauses:                    5199
% 11.54/2.00  inst_num_in_passive:                    2161
% 11.54/2.00  inst_num_in_active:                     1643
% 11.54/2.00  inst_num_in_unprocessed:                1395
% 11.54/2.00  inst_num_of_loops:                      1720
% 11.54/2.00  inst_num_of_learning_restarts:          0
% 11.54/2.00  inst_num_moves_active_passive:          71
% 11.54/2.00  inst_lit_activity:                      0
% 11.54/2.00  inst_lit_activity_moves:                0
% 11.54/2.00  inst_num_tautologies:                   0
% 11.54/2.00  inst_num_prop_implied:                  0
% 11.54/2.00  inst_num_existing_simplified:           0
% 11.54/2.00  inst_num_eq_res_simplified:             0
% 11.54/2.00  inst_num_child_elim:                    0
% 11.54/2.00  inst_num_of_dismatching_blockings:      2500
% 11.54/2.00  inst_num_of_non_proper_insts:           5558
% 11.54/2.00  inst_num_of_duplicates:                 0
% 11.54/2.00  inst_inst_num_from_inst_to_res:         0
% 11.54/2.00  inst_dismatching_checking_time:         0.
% 11.54/2.00  
% 11.54/2.00  ------ Resolution
% 11.54/2.00  
% 11.54/2.00  res_num_of_clauses:                     0
% 11.54/2.00  res_num_in_passive:                     0
% 11.54/2.00  res_num_in_active:                      0
% 11.54/2.00  res_num_of_loops:                       120
% 11.54/2.00  res_forward_subset_subsumed:            399
% 11.54/2.00  res_backward_subset_subsumed:           10
% 11.54/2.00  res_forward_subsumed:                   0
% 11.54/2.00  res_backward_subsumed:                  0
% 11.54/2.00  res_forward_subsumption_resolution:     0
% 11.54/2.00  res_backward_subsumption_resolution:    0
% 11.54/2.00  res_clause_to_clause_subsumption:       13714
% 11.54/2.00  res_orphan_elimination:                 0
% 11.54/2.00  res_tautology_del:                      514
% 11.54/2.00  res_num_eq_res_simplified:              0
% 11.54/2.00  res_num_sel_changes:                    0
% 11.54/2.00  res_moves_from_active_to_pass:          0
% 11.54/2.00  
% 11.54/2.00  ------ Superposition
% 11.54/2.00  
% 11.54/2.00  sup_time_total:                         0.
% 11.54/2.00  sup_time_generating:                    0.
% 11.54/2.00  sup_time_sim_full:                      0.
% 11.54/2.00  sup_time_sim_immed:                     0.
% 11.54/2.00  
% 11.54/2.00  sup_num_of_clauses:                     1039
% 11.54/2.00  sup_num_in_active:                      312
% 11.54/2.00  sup_num_in_passive:                     727
% 11.54/2.00  sup_num_of_loops:                       343
% 11.54/2.00  sup_fw_superposition:                   3906
% 11.54/2.00  sup_bw_superposition:                   2719
% 11.54/2.00  sup_immediate_simplified:               2701
% 11.54/2.00  sup_given_eliminated:                   4
% 11.54/2.00  comparisons_done:                       0
% 11.54/2.00  comparisons_avoided:                    6
% 11.54/2.00  
% 11.54/2.00  ------ Simplifications
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  sim_fw_subset_subsumed:                 45
% 11.54/2.00  sim_bw_subset_subsumed:                 7
% 11.54/2.00  sim_fw_subsumed:                        661
% 11.54/2.00  sim_bw_subsumed:                        37
% 11.54/2.00  sim_fw_subsumption_res:                 0
% 11.54/2.00  sim_bw_subsumption_res:                 0
% 11.54/2.00  sim_tautology_del:                      25
% 11.54/2.00  sim_eq_tautology_del:                   723
% 11.54/2.00  sim_eq_res_simp:                        2
% 11.54/2.00  sim_fw_demodulated:                     1659
% 11.54/2.00  sim_bw_demodulated:                     89
% 11.54/2.00  sim_light_normalised:                   853
% 11.54/2.00  sim_joinable_taut:                      0
% 11.54/2.00  sim_joinable_simp:                      0
% 11.54/2.00  sim_ac_normalised:                      0
% 11.54/2.00  sim_smt_subsumption:                    0
% 11.54/2.00  
%------------------------------------------------------------------------------
