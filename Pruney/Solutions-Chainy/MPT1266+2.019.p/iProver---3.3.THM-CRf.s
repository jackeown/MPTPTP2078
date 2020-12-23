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
% DateTime   : Thu Dec  3 12:15:00 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  159 (1169 expanded)
%              Number of clauses        :   84 ( 381 expanded)
%              Number of leaves         :   23 ( 264 expanded)
%              Depth                    :   30
%              Number of atoms          :  372 (3760 expanded)
%              Number of equality atoms :  221 (1530 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f67,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f74])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_623,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_611,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_609,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_618,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_969,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_618])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_620,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1124,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_969,c_620])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_610,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1336,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1124,c_610])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_613,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1342,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_613])).

cnf(c_1343,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1342,c_1124])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1343,c_18])).

cnf(c_1642,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1641])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_615,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2136,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_615])).

cnf(c_2455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2136,c_18])).

cnf(c_2456,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2455])).

cnf(c_2464,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_2456])).

cnf(c_12772,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_2464])).

cnf(c_13283,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_12772])).

cnf(c_13502,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_611,c_13283])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_617,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2855,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_617])).

cnf(c_2859,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2855,c_1124])).

cnf(c_3326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_18])).

cnf(c_3327,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3326])).

cnf(c_3336,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1336,c_3327])).

cnf(c_13511,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_13502,c_3336])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_621,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_624,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1919,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_621,c_624])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1931,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1919,c_0,c_1])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_622,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1128,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_621,c_622])).

cnf(c_2089,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1931,c_1128])).

cnf(c_13514,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13511,c_2089])).

cnf(c_13663,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13514,c_3336])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_619,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1894,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_619])).

cnf(c_1905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1894,c_1124])).

cnf(c_2319,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1905,c_18])).

cnf(c_2320,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2319])).

cnf(c_2328,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_622])).

cnf(c_4413,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_2328])).

cnf(c_13822,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1336,c_4413])).

cnf(c_14163,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_13663,c_13822])).

cnf(c_14164,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_14163,c_1931])).

cnf(c_10,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_616,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15010,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14164,c_616])).

cnf(c_15027,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15010,c_1124])).

cnf(c_15395,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15027,c_18])).

cnf(c_15396,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15395])).

cnf(c_15401,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_15396])).

cnf(c_15635,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15401,c_1336])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_614,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1773,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_614])).

cnf(c_1778,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1773,c_1124])).

cnf(c_2593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_18])).

cnf(c_2594,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2593])).

cnf(c_15641,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15635,c_2594])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_612,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13665,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13514,c_612])).

cnf(c_13666,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13665])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15641,c_13666,c_1336])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.03/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.03  
% 4.03/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/1.03  
% 4.03/1.03  ------  iProver source info
% 4.03/1.03  
% 4.03/1.03  git: date: 2020-06-30 10:37:57 +0100
% 4.03/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/1.03  git: non_committed_changes: false
% 4.03/1.03  git: last_make_outside_of_git: false
% 4.03/1.03  
% 4.03/1.03  ------ 
% 4.03/1.03  ------ Parsing...
% 4.03/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/1.03  
% 4.03/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.03/1.03  
% 4.03/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/1.03  
% 4.03/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/1.03  ------ Proving...
% 4.03/1.03  ------ Problem Properties 
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  clauses                                 18
% 4.03/1.03  conjectures                             4
% 4.03/1.03  EPR                                     2
% 4.03/1.03  Horn                                    17
% 4.03/1.03  unary                                   5
% 4.03/1.03  binary                                  7
% 4.03/1.03  lits                                    41
% 4.03/1.03  lits eq                                 10
% 4.03/1.03  fd_pure                                 0
% 4.03/1.03  fd_pseudo                               0
% 4.03/1.03  fd_cond                                 0
% 4.03/1.03  fd_pseudo_cond                          0
% 4.03/1.03  AC symbols                              0
% 4.03/1.03  
% 4.03/1.03  ------ Input Options Time Limit: Unbounded
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  ------ 
% 4.03/1.03  Current options:
% 4.03/1.03  ------ 
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  ------ Proving...
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  % SZS status Theorem for theBenchmark.p
% 4.03/1.03  
% 4.03/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/1.03  
% 4.03/1.03  fof(f11,axiom,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f26,plain,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.03/1.03    inference(ennf_transformation,[],[f11])).
% 4.03/1.03  
% 4.03/1.03  fof(f53,plain,(
% 4.03/1.03    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f26])).
% 4.03/1.03  
% 4.03/1.03  fof(f22,conjecture,(
% 4.03/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f23,negated_conjecture,(
% 4.03/1.03    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 4.03/1.03    inference(negated_conjecture,[],[f22])).
% 4.03/1.03  
% 4.03/1.03  fof(f35,plain,(
% 4.03/1.03    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f23])).
% 4.03/1.03  
% 4.03/1.03  fof(f38,plain,(
% 4.03/1.03    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.03/1.03    inference(nnf_transformation,[],[f35])).
% 4.03/1.03  
% 4.03/1.03  fof(f39,plain,(
% 4.03/1.03    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.03/1.03    inference(flattening,[],[f38])).
% 4.03/1.03  
% 4.03/1.03  fof(f41,plain,(
% 4.03/1.03    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.03/1.03    introduced(choice_axiom,[])).
% 4.03/1.03  
% 4.03/1.03  fof(f40,plain,(
% 4.03/1.03    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.03/1.03    introduced(choice_axiom,[])).
% 4.03/1.03  
% 4.03/1.03  fof(f42,plain,(
% 4.03/1.03    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.03/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 4.03/1.03  
% 4.03/1.03  fof(f67,plain,(
% 4.03/1.03    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 4.03/1.03    inference(cnf_transformation,[],[f42])).
% 4.03/1.03  
% 4.03/1.03  fof(f65,plain,(
% 4.03/1.03    l1_pre_topc(sK0)),
% 4.03/1.03    inference(cnf_transformation,[],[f42])).
% 4.03/1.03  
% 4.03/1.03  fof(f18,axiom,(
% 4.03/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f31,plain,(
% 4.03/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f18])).
% 4.03/1.03  
% 4.03/1.03  fof(f59,plain,(
% 4.03/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f31])).
% 4.03/1.03  
% 4.03/1.03  fof(f16,axiom,(
% 4.03/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f28,plain,(
% 4.03/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f16])).
% 4.03/1.03  
% 4.03/1.03  fof(f57,plain,(
% 4.03/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f28])).
% 4.03/1.03  
% 4.03/1.03  fof(f66,plain,(
% 4.03/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.03/1.03    inference(cnf_transformation,[],[f42])).
% 4.03/1.03  
% 4.03/1.03  fof(f21,axiom,(
% 4.03/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f34,plain,(
% 4.03/1.03    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f21])).
% 4.03/1.03  
% 4.03/1.03  fof(f37,plain,(
% 4.03/1.03    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(nnf_transformation,[],[f34])).
% 4.03/1.03  
% 4.03/1.03  fof(f63,plain,(
% 4.03/1.03    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f37])).
% 4.03/1.03  
% 4.03/1.03  fof(f20,axiom,(
% 4.03/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f33,plain,(
% 4.03/1.03    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f20])).
% 4.03/1.03  
% 4.03/1.03  fof(f36,plain,(
% 4.03/1.03    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(nnf_transformation,[],[f33])).
% 4.03/1.03  
% 4.03/1.03  fof(f61,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f36])).
% 4.03/1.03  
% 4.03/1.03  fof(f19,axiom,(
% 4.03/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f32,plain,(
% 4.03/1.03    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(ennf_transformation,[],[f19])).
% 4.03/1.03  
% 4.03/1.03  fof(f60,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f32])).
% 4.03/1.03  
% 4.03/1.03  fof(f13,axiom,(
% 4.03/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f55,plain,(
% 4.03/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f13])).
% 4.03/1.03  
% 4.03/1.03  fof(f10,axiom,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f25,plain,(
% 4.03/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.03/1.03    inference(ennf_transformation,[],[f10])).
% 4.03/1.03  
% 4.03/1.03  fof(f52,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f25])).
% 4.03/1.03  
% 4.03/1.03  fof(f1,axiom,(
% 4.03/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f43,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f1])).
% 4.03/1.03  
% 4.03/1.03  fof(f14,axiom,(
% 4.03/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f56,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f14])).
% 4.03/1.03  
% 4.03/1.03  fof(f4,axiom,(
% 4.03/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f46,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f4])).
% 4.03/1.03  
% 4.03/1.03  fof(f5,axiom,(
% 4.03/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f47,plain,(
% 4.03/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f5])).
% 4.03/1.03  
% 4.03/1.03  fof(f6,axiom,(
% 4.03/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f48,plain,(
% 4.03/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f6])).
% 4.03/1.03  
% 4.03/1.03  fof(f7,axiom,(
% 4.03/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f49,plain,(
% 4.03/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f7])).
% 4.03/1.03  
% 4.03/1.03  fof(f8,axiom,(
% 4.03/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f50,plain,(
% 4.03/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f8])).
% 4.03/1.03  
% 4.03/1.03  fof(f9,axiom,(
% 4.03/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f51,plain,(
% 4.03/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f9])).
% 4.03/1.03  
% 4.03/1.03  fof(f69,plain,(
% 4.03/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.03/1.03    inference(definition_unfolding,[],[f50,f51])).
% 4.03/1.03  
% 4.03/1.03  fof(f70,plain,(
% 4.03/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.03/1.03    inference(definition_unfolding,[],[f49,f69])).
% 4.03/1.03  
% 4.03/1.03  fof(f71,plain,(
% 4.03/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.03/1.03    inference(definition_unfolding,[],[f48,f70])).
% 4.03/1.03  
% 4.03/1.03  fof(f72,plain,(
% 4.03/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.03/1.03    inference(definition_unfolding,[],[f47,f71])).
% 4.03/1.03  
% 4.03/1.03  fof(f73,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.03/1.03    inference(definition_unfolding,[],[f46,f72])).
% 4.03/1.03  
% 4.03/1.03  fof(f74,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.03/1.03    inference(definition_unfolding,[],[f56,f73])).
% 4.03/1.03  
% 4.03/1.03  fof(f75,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.03/1.03    inference(definition_unfolding,[],[f43,f74])).
% 4.03/1.03  
% 4.03/1.03  fof(f77,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/1.03    inference(definition_unfolding,[],[f52,f75])).
% 4.03/1.03  
% 4.03/1.03  fof(f2,axiom,(
% 4.03/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f44,plain,(
% 4.03/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.03/1.03    inference(cnf_transformation,[],[f2])).
% 4.03/1.03  
% 4.03/1.03  fof(f76,plain,(
% 4.03/1.03    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 4.03/1.03    inference(definition_unfolding,[],[f44,f74])).
% 4.03/1.03  
% 4.03/1.03  fof(f3,axiom,(
% 4.03/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f45,plain,(
% 4.03/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.03/1.03    inference(cnf_transformation,[],[f3])).
% 4.03/1.03  
% 4.03/1.03  fof(f12,axiom,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f27,plain,(
% 4.03/1.03    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.03/1.03    inference(ennf_transformation,[],[f12])).
% 4.03/1.03  
% 4.03/1.03  fof(f54,plain,(
% 4.03/1.03    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/1.03    inference(cnf_transformation,[],[f27])).
% 4.03/1.03  
% 4.03/1.03  fof(f17,axiom,(
% 4.03/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.03/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.03  
% 4.03/1.03  fof(f29,plain,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.03/1.03    inference(ennf_transformation,[],[f17])).
% 4.03/1.03  
% 4.03/1.03  fof(f30,plain,(
% 4.03/1.03    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.03/1.03    inference(flattening,[],[f29])).
% 4.03/1.03  
% 4.03/1.03  fof(f58,plain,(
% 4.03/1.03    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f30])).
% 4.03/1.03  
% 4.03/1.03  fof(f62,plain,(
% 4.03/1.03    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f36])).
% 4.03/1.03  
% 4.03/1.03  fof(f64,plain,(
% 4.03/1.03    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/1.03    inference(cnf_transformation,[],[f37])).
% 4.03/1.03  
% 4.03/1.03  fof(f68,plain,(
% 4.03/1.03    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 4.03/1.03    inference(cnf_transformation,[],[f42])).
% 4.03/1.03  
% 4.03/1.03  cnf(c_3,plain,
% 4.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/1.03      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.03/1.03      inference(cnf_transformation,[],[f53]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_623,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.03/1.03      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15,negated_conjecture,
% 4.03/1.03      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f67]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_611,plain,
% 4.03/1.03      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 4.03/1.03      | v2_tops_1(sK1,sK0) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_17,negated_conjecture,
% 4.03/1.03      ( l1_pre_topc(sK0) ),
% 4.03/1.03      inference(cnf_transformation,[],[f65]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_609,plain,
% 4.03/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_8,plain,
% 4.03/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.03/1.03      inference(cnf_transformation,[],[f59]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_618,plain,
% 4.03/1.03      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_969,plain,
% 4.03/1.03      ( l1_struct_0(sK0) = iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_609,c_618]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_6,plain,
% 4.03/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.03/1.03      inference(cnf_transformation,[],[f57]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_620,plain,
% 4.03/1.03      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.03/1.03      | l1_struct_0(X0) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1124,plain,
% 4.03/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_969,c_620]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_16,negated_conjecture,
% 4.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.03/1.03      inference(cnf_transformation,[],[f66]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_610,plain,
% 4.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1336,plain,
% 4.03/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_1124,c_610]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13,plain,
% 4.03/1.03      ( ~ v2_tops_1(X0,X1)
% 4.03/1.03      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 4.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f63]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_613,plain,
% 4.03/1.03      ( v2_tops_1(X0,X1) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.03/1.03      | l1_pre_topc(X1) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1342,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1124,c_613]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1343,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_1342,c_1124]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_18,plain,
% 4.03/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1641,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 4.03/1.03      | v2_tops_1(X0,sK0) != iProver_top ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_1343,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1642,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_1641]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_11,plain,
% 4.03/1.03      ( ~ v1_tops_1(X0,X1)
% 4.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1)
% 4.03/1.03      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f61]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_615,plain,
% 4.03/1.03      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 4.03/1.03      | v1_tops_1(X1,X0) != iProver_top
% 4.03/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(X0) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2136,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 4.03/1.03      | v1_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1124,c_615]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2455,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | v1_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_2136,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2456,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 4.03/1.03      | v1_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_2455]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2464,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_623,c_2456]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_12772,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 4.03/1.03      | v2_tops_1(X0,sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1642,c_2464]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13283,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 4.03/1.03      | v2_tops_1(sK1,sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1336,c_12772]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13502,plain,
% 4.03/1.03      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.03/1.03      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_611,c_13283]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_9,plain,
% 4.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1)
% 4.03/1.03      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 4.03/1.03      inference(cnf_transformation,[],[f60]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_617,plain,
% 4.03/1.03      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 4.03/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(X0) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2855,plain,
% 4.03/1.03      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1124,c_617]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2859,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_2855,c_1124]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_3326,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_2859,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_3327,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_3326]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_3336,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1336,c_3327]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13511,plain,
% 4.03/1.03      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.03/1.03      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_13502,c_3336]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_5,plain,
% 4.03/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.03/1.03      inference(cnf_transformation,[],[f55]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_621,plain,
% 4.03/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2,plain,
% 4.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/1.03      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 4.03/1.03      inference(cnf_transformation,[],[f77]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_624,plain,
% 4.03/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 4.03/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1919,plain,
% 4.03/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_621,c_624]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_0,plain,
% 4.03/1.03      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.03/1.03      inference(cnf_transformation,[],[f76]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1,plain,
% 4.03/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.03/1.03      inference(cnf_transformation,[],[f45]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1931,plain,
% 4.03/1.03      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_1919,c_0,c_1]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_4,plain,
% 4.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/1.03      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.03/1.03      inference(cnf_transformation,[],[f54]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_622,plain,
% 4.03/1.03      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.03/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1128,plain,
% 4.03/1.03      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_621,c_622]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2089,plain,
% 4.03/1.03      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_1931,c_1128]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13514,plain,
% 4.03/1.03      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_13511,c_2089]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13663,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_13514,c_3336]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_7,plain,
% 4.03/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f58]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_619,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.03/1.03      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.03/1.03      | l1_pre_topc(X1) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1894,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/1.03      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1124,c_619]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1905,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_1894,c_1124]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2319,plain,
% 4.03/1.03      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_1905,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2320,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_2319]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2328,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_2320,c_622]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_4413,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_623,c_2328]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13822,plain,
% 4.03/1.03      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1336,c_4413]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_14163,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_13663,c_13822]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_14164,plain,
% 4.03/1.03      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_14163,c_1931]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_10,plain,
% 4.03/1.03      ( v1_tops_1(X0,X1)
% 4.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1)
% 4.03/1.03      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f62]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_616,plain,
% 4.03/1.03      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 4.03/1.03      | v1_tops_1(X1,X0) = iProver_top
% 4.03/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(X0) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15010,plain,
% 4.03/1.03      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_14164,c_616]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15027,plain,
% 4.03/1.03      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_15010,c_1124]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15395,plain,
% 4.03/1.03      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_15027,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15396,plain,
% 4.03/1.03      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_15395]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15401,plain,
% 4.03/1.03      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_623,c_15396]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15635,plain,
% 4.03/1.03      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_15401,c_1336]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_12,plain,
% 4.03/1.03      ( v2_tops_1(X0,X1)
% 4.03/1.03      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 4.03/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/1.03      | ~ l1_pre_topc(X1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f64]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_614,plain,
% 4.03/1.03      ( v2_tops_1(X0,X1) = iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.03/1.03      | l1_pre_topc(X1) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1773,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) = iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_1124,c_614]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_1778,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) = iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/1.03      inference(light_normalisation,[status(thm)],[c_1773,c_1124]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2593,plain,
% 4.03/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 4.03/1.03      | v2_tops_1(X0,sK0) = iProver_top ),
% 4.03/1.03      inference(global_propositional_subsumption,
% 4.03/1.03                [status(thm)],
% 4.03/1.03                [c_1778,c_18]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_2594,plain,
% 4.03/1.03      ( v2_tops_1(X0,sK0) = iProver_top
% 4.03/1.03      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 4.03/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(renaming,[status(thm)],[c_2593]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_15641,plain,
% 4.03/1.03      ( v2_tops_1(sK1,sK0) = iProver_top
% 4.03/1.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 4.03/1.03      inference(superposition,[status(thm)],[c_15635,c_2594]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_14,negated_conjecture,
% 4.03/1.03      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 4.03/1.03      inference(cnf_transformation,[],[f68]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_612,plain,
% 4.03/1.03      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 4.03/1.03      | v2_tops_1(sK1,sK0) != iProver_top ),
% 4.03/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13665,plain,
% 4.03/1.03      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 4.03/1.03      inference(demodulation,[status(thm)],[c_13514,c_612]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(c_13666,plain,
% 4.03/1.03      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 4.03/1.03      inference(equality_resolution_simp,[status(thm)],[c_13665]) ).
% 4.03/1.03  
% 4.03/1.03  cnf(contradiction,plain,
% 4.03/1.03      ( $false ),
% 4.03/1.03      inference(minisat,[status(thm)],[c_15641,c_13666,c_1336]) ).
% 4.03/1.03  
% 4.03/1.03  
% 4.03/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/1.03  
% 4.03/1.03  ------                               Statistics
% 4.03/1.03  
% 4.03/1.03  ------ Selected
% 4.03/1.03  
% 4.03/1.03  total_time:                             0.514
% 4.03/1.03  
%------------------------------------------------------------------------------
