%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:59 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  185 (1296 expanded)
%              Number of clauses        :   95 ( 420 expanded)
%              Number of leaves         :   27 ( 292 expanded)
%              Depth                    :   30
%              Number of atoms          :  424 (4207 expanded)
%              Number of equality atoms :  250 (1699 expanded)
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

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).

fof(f77,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f60,f86])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_702,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_700,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_711,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1064,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_711])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_713,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1230,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1064,c_713])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_701,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1607,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_701])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_705,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2023,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_705])).

cnf(c_2028,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2023,c_1230])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_20])).

cnf(c_4349,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4348])).

cnf(c_12,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_707,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2519,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_707])).

cnf(c_3861,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2519,c_20])).

cnf(c_3862,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3861])).

cnf(c_3870,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_3862])).

cnf(c_12678,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4349,c_3870])).

cnf(c_13788,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_12678])).

cnf(c_13854,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_702,c_13788])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_709,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3543,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_709])).

cnf(c_3547,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3543,c_1230])).

cnf(c_4070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3547,c_20])).

cnf(c_4071,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4070])).

cnf(c_4080,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1607,c_4071])).

cnf(c_13997,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_13854,c_4080])).

cnf(c_3,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_716,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_716,c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1992,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_710])).

cnf(c_2864,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1992,c_20])).

cnf(c_2865,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2864])).

cnf(c_2873,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_2865])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_704,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1226,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_700,c_704])).

cnf(c_2878,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2873,c_1226])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_718,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3044,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2878,c_718])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_717,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2254,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_725,c_717])).

cnf(c_4745,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3044,c_2254])).

cnf(c_14000,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13997,c_4745])).

cnf(c_14015,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14000,c_4080])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_712])).

cnf(c_2233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2208,c_1230])).

cnf(c_3315,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_20])).

cnf(c_3316,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3315])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_714,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3326,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_714])).

cnf(c_7163,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_3326])).

cnf(c_14350,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1607,c_7163])).

cnf(c_14689,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_14015,c_14350])).

cnf(c_14690,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_14689,c_1])).

cnf(c_11,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_708,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15649,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14690,c_708])).

cnf(c_15682,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15649,c_1230])).

cnf(c_16084,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15682,c_20])).

cnf(c_16085,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16084])).

cnf(c_16090,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_16085])).

cnf(c_16098,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16090,c_1607])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_706,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3501,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_706])).

cnf(c_3506,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3501,c_1230])).

cnf(c_5437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3506,c_20])).

cnf(c_5438,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5437])).

cnf(c_16104,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16098,c_5438])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_703,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14017,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14000,c_703])).

cnf(c_14018,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14017])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16104,c_14018,c_1607])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.64/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.50  
% 7.64/1.50  ------  iProver source info
% 7.64/1.50  
% 7.64/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.50  git: non_committed_changes: false
% 7.64/1.50  git: last_make_outside_of_git: false
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  ------ Parsing...
% 7.64/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.50  ------ Proving...
% 7.64/1.50  ------ Problem Properties 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  clauses                                 20
% 7.64/1.50  conjectures                             4
% 7.64/1.50  EPR                                     2
% 7.64/1.50  Horn                                    19
% 7.64/1.50  unary                                   4
% 7.64/1.50  binary                                  9
% 7.64/1.50  lits                                    47
% 7.64/1.50  lits eq                                 11
% 7.64/1.50  fd_pure                                 0
% 7.64/1.50  fd_pseudo                               0
% 7.64/1.50  fd_cond                                 0
% 7.64/1.50  fd_pseudo_cond                          0
% 7.64/1.50  AC symbols                              0
% 7.64/1.50  
% 7.64/1.50  ------ Input Options Time Limit: Unbounded
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  Current options:
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ Proving...
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS status Theorem for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  fof(f13,axiom,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f30,plain,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f13])).
% 7.64/1.50  
% 7.64/1.50  fof(f61,plain,(
% 7.64/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f30])).
% 7.64/1.50  
% 7.64/1.50  fof(f25,conjecture,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f26,negated_conjecture,(
% 7.64/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.64/1.50    inference(negated_conjecture,[],[f25])).
% 7.64/1.50  
% 7.64/1.50  fof(f41,plain,(
% 7.64/1.50    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f26])).
% 7.64/1.50  
% 7.64/1.50  fof(f44,plain,(
% 7.64/1.50    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f41])).
% 7.64/1.50  
% 7.64/1.50  fof(f45,plain,(
% 7.64/1.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.50    inference(flattening,[],[f44])).
% 7.64/1.50  
% 7.64/1.50  fof(f47,plain,(
% 7.64/1.50    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f46,plain,(
% 7.64/1.50    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f48,plain,(
% 7.64/1.50    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).
% 7.64/1.50  
% 7.64/1.50  fof(f77,plain,(
% 7.64/1.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 7.64/1.50    inference(cnf_transformation,[],[f48])).
% 7.64/1.50  
% 7.64/1.50  fof(f75,plain,(
% 7.64/1.50    l1_pre_topc(sK0)),
% 7.64/1.50    inference(cnf_transformation,[],[f48])).
% 7.64/1.50  
% 7.64/1.50  fof(f19,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f35,plain,(
% 7.64/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f19])).
% 7.64/1.50  
% 7.64/1.50  fof(f67,plain,(
% 7.64/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f35])).
% 7.64/1.50  
% 7.64/1.50  fof(f17,axiom,(
% 7.64/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f32,plain,(
% 7.64/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f17])).
% 7.64/1.50  
% 7.64/1.50  fof(f65,plain,(
% 7.64/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f32])).
% 7.64/1.50  
% 7.64/1.50  fof(f76,plain,(
% 7.64/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.64/1.50    inference(cnf_transformation,[],[f48])).
% 7.64/1.50  
% 7.64/1.50  fof(f23,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f39,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f23])).
% 7.64/1.50  
% 7.64/1.50  fof(f43,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f39])).
% 7.64/1.50  
% 7.64/1.50  fof(f72,plain,(
% 7.64/1.50    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f43])).
% 7.64/1.50  
% 7.64/1.50  fof(f22,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f38,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f22])).
% 7.64/1.50  
% 7.64/1.50  fof(f42,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f38])).
% 7.64/1.50  
% 7.64/1.50  fof(f70,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f42])).
% 7.64/1.50  
% 7.64/1.50  fof(f21,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f37,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f21])).
% 7.64/1.50  
% 7.64/1.50  fof(f69,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f37])).
% 7.64/1.50  
% 7.64/1.50  fof(f12,axiom,(
% 7.64/1.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f60,plain,(
% 7.64/1.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f12])).
% 7.64/1.50  
% 7.64/1.50  fof(f15,axiom,(
% 7.64/1.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f63,plain,(
% 7.64/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f15])).
% 7.64/1.50  
% 7.64/1.50  fof(f9,axiom,(
% 7.64/1.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f57,plain,(
% 7.64/1.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f9])).
% 7.64/1.50  
% 7.64/1.50  fof(f86,plain,(
% 7.64/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f63,f57])).
% 7.64/1.50  
% 7.64/1.50  fof(f90,plain,(
% 7.64/1.50    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(definition_unfolding,[],[f60,f86])).
% 7.64/1.50  
% 7.64/1.50  fof(f10,axiom,(
% 7.64/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f58,plain,(
% 7.64/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.64/1.50    inference(cnf_transformation,[],[f10])).
% 7.64/1.50  
% 7.64/1.50  fof(f88,plain,(
% 7.64/1.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.64/1.50    inference(definition_unfolding,[],[f58,f86])).
% 7.64/1.50  
% 7.64/1.50  fof(f20,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f36,plain,(
% 7.64/1.50    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f20])).
% 7.64/1.50  
% 7.64/1.50  fof(f68,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f36])).
% 7.64/1.50  
% 7.64/1.50  fof(f24,axiom,(
% 7.64/1.50    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f40,plain,(
% 7.64/1.50    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f24])).
% 7.64/1.50  
% 7.64/1.50  fof(f74,plain,(
% 7.64/1.50    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f40])).
% 7.64/1.50  
% 7.64/1.50  fof(f1,axiom,(
% 7.64/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f27,plain,(
% 7.64/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 7.64/1.50    inference(unused_predicate_definition_removal,[],[f1])).
% 7.64/1.50  
% 7.64/1.50  fof(f28,plain,(
% 7.64/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 7.64/1.50    inference(ennf_transformation,[],[f27])).
% 7.64/1.50  
% 7.64/1.50  fof(f49,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f28])).
% 7.64/1.50  
% 7.64/1.50  fof(f2,axiom,(
% 7.64/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f50,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f2])).
% 7.64/1.50  
% 7.64/1.50  fof(f16,axiom,(
% 7.64/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f64,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f16])).
% 7.64/1.50  
% 7.64/1.50  fof(f3,axiom,(
% 7.64/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f51,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f3])).
% 7.64/1.50  
% 7.64/1.50  fof(f4,axiom,(
% 7.64/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f52,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f4])).
% 7.64/1.50  
% 7.64/1.50  fof(f5,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f53,plain,(
% 7.64/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f5])).
% 7.64/1.50  
% 7.64/1.50  fof(f6,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f54,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f6])).
% 7.64/1.50  
% 7.64/1.50  fof(f7,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f55,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f7])).
% 7.64/1.50  
% 7.64/1.50  fof(f8,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f56,plain,(
% 7.64/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f8])).
% 7.64/1.50  
% 7.64/1.50  fof(f79,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f55,f56])).
% 7.64/1.50  
% 7.64/1.50  fof(f80,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f54,f79])).
% 7.64/1.50  
% 7.64/1.50  fof(f81,plain,(
% 7.64/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f53,f80])).
% 7.64/1.50  
% 7.64/1.50  fof(f82,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f52,f81])).
% 7.64/1.50  
% 7.64/1.50  fof(f83,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f51,f82])).
% 7.64/1.50  
% 7.64/1.50  fof(f84,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.64/1.50    inference(definition_unfolding,[],[f64,f83])).
% 7.64/1.50  
% 7.64/1.50  fof(f85,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.64/1.50    inference(definition_unfolding,[],[f50,f84])).
% 7.64/1.50  
% 7.64/1.50  fof(f87,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f49,f85])).
% 7.64/1.50  
% 7.64/1.50  fof(f11,axiom,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f29,plain,(
% 7.64/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f11])).
% 7.64/1.50  
% 7.64/1.50  fof(f59,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f89,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(definition_unfolding,[],[f59,f85])).
% 7.64/1.50  
% 7.64/1.50  fof(f18,axiom,(
% 7.64/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f33,plain,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f18])).
% 7.64/1.50  
% 7.64/1.50  fof(f34,plain,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.64/1.50    inference(flattening,[],[f33])).
% 7.64/1.50  
% 7.64/1.50  fof(f66,plain,(
% 7.64/1.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f34])).
% 7.64/1.50  
% 7.64/1.50  fof(f14,axiom,(
% 7.64/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f31,plain,(
% 7.64/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f14])).
% 7.64/1.50  
% 7.64/1.50  fof(f62,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f31])).
% 7.64/1.50  
% 7.64/1.50  fof(f71,plain,(
% 7.64/1.50    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f42])).
% 7.64/1.50  
% 7.64/1.50  fof(f73,plain,(
% 7.64/1.50    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f43])).
% 7.64/1.50  
% 7.64/1.50  fof(f78,plain,(
% 7.64/1.50    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 7.64/1.50    inference(cnf_transformation,[],[f48])).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_715,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.64/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_17,negated_conjecture,
% 7.64/1.50      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_702,plain,
% 7.64/1.50      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 7.64/1.50      | v2_tops_1(sK1,sK0) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_19,negated_conjecture,
% 7.64/1.50      ( l1_pre_topc(sK0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_700,plain,
% 7.64/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_8,plain,
% 7.64/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_711,plain,
% 7.64/1.50      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1064,plain,
% 7.64/1.50      ( l1_struct_0(sK0) = iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_700,c_711]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6,plain,
% 7.64/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_713,plain,
% 7.64/1.50      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.64/1.50      | l1_struct_0(X0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1230,plain,
% 7.64/1.50      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1064,c_713]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_18,negated_conjecture,
% 7.64/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.64/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_701,plain,
% 7.64/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1607,plain,
% 7.64/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_1230,c_701]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14,plain,
% 7.64/1.50      ( ~ v2_tops_1(X0,X1)
% 7.64/1.50      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 7.64/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_705,plain,
% 7.64/1.50      ( v2_tops_1(X0,X1) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.64/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2023,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_705]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2028,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_2023,c_1230]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_20,plain,
% 7.64/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4348,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 7.64/1.50      | v2_tops_1(X0,sK0) != iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_2028,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4349,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_4348]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_12,plain,
% 7.64/1.50      ( ~ v1_tops_1(X0,X1)
% 7.64/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1)
% 7.64/1.50      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_707,plain,
% 7.64/1.50      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 7.64/1.50      | v1_tops_1(X1,X0) != iProver_top
% 7.64/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2519,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 7.64/1.50      | v1_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_707]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3861,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | v1_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_2519,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3862,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 7.64/1.50      | v1_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_3861]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3870,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_715,c_3862]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_12678,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 7.64/1.50      | v2_tops_1(X0,sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_4349,c_3870]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_13788,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 7.64/1.50      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1607,c_12678]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_13854,plain,
% 7.64/1.50      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.64/1.50      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_702,c_13788]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_10,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1)
% 7.64/1.50      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_709,plain,
% 7.64/1.50      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 7.64/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3543,plain,
% 7.64/1.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_709]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3547,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_3543,c_1230]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4070,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_3547,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4071,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_4070]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4080,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1607,c_4071]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_13997,plain,
% 7.64/1.50      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.64/1.50      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_13854,c_4080]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3,plain,
% 7.64/1.50      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_716,plain,
% 7.64/1.50      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1,plain,
% 7.64/1.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_725,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_716,c_1]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_9,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.64/1.50      | ~ l1_pre_topc(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_710,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.64/1.50      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 7.64/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1992,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_710]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2864,plain,
% 7.64/1.50      ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_1992,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2865,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_2864]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2873,plain,
% 7.64/1.50      ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_725,c_2865]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_15,plain,
% 7.64/1.50      ( ~ l1_pre_topc(X0)
% 7.64/1.50      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_704,plain,
% 7.64/1.50      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 7.64/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1226,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_700,c_704]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2878,plain,
% 7.64/1.50      ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_2873,c_1226]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_0,plain,
% 7.64/1.50      ( ~ r1_tarski(X0,X1)
% 7.64/1.50      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_718,plain,
% 7.64/1.50      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
% 7.64/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3044,plain,
% 7.64/1.50      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))) = k1_xboole_0 ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_2878,c_718]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.50      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_717,plain,
% 7.64/1.50      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 7.64/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2254,plain,
% 7.64/1.50      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_725,c_717]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4745,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_3044,c_2254]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14000,plain,
% 7.64/1.50      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_13997,c_4745]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14015,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_14000,c_4080]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_712,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.64/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.64/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2208,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.64/1.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_712]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2233,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_2208,c_1230]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3315,plain,
% 7.64/1.50      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_2233,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3316,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_3315]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5,plain,
% 7.64/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_714,plain,
% 7.64/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.64/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3326,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_3316,c_714]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7163,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_715,c_3326]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14350,plain,
% 7.64/1.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1607,c_7163]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14689,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_14015,c_14350]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14690,plain,
% 7.64/1.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_14689,c_1]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_11,plain,
% 7.64/1.50      ( v1_tops_1(X0,X1)
% 7.64/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1)
% 7.64/1.50      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_708,plain,
% 7.64/1.50      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 7.64/1.50      | v1_tops_1(X1,X0) = iProver_top
% 7.64/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_15649,plain,
% 7.64/1.50      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_14690,c_708]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_15682,plain,
% 7.64/1.50      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_15649,c_1230]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16084,plain,
% 7.64/1.50      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_15682,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16085,plain,
% 7.64/1.50      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_16084]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16090,plain,
% 7.64/1.50      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_715,c_16085]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16098,plain,
% 7.64/1.50      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_16090,c_1607]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_13,plain,
% 7.64/1.50      ( v2_tops_1(X0,X1)
% 7.64/1.50      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 7.64/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.64/1.50      | ~ l1_pre_topc(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_706,plain,
% 7.64/1.50      ( v2_tops_1(X0,X1) = iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.64/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3501,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) = iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_1230,c_706]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3506,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) = iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.64/1.50      inference(light_normalisation,[status(thm)],[c_3501,c_1230]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5437,plain,
% 7.64/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 7.64/1.50      | v2_tops_1(X0,sK0) = iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_3506,c_20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5438,plain,
% 7.64/1.50      ( v2_tops_1(X0,sK0) = iProver_top
% 7.64/1.50      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 7.64/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_5437]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16104,plain,
% 7.64/1.50      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.64/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_16098,c_5438]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_16,negated_conjecture,
% 7.64/1.50      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_703,plain,
% 7.64/1.50      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 7.64/1.50      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14017,plain,
% 7.64/1.50      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_14000,c_703]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14018,plain,
% 7.64/1.50      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 7.64/1.50      inference(equality_resolution_simp,[status(thm)],[c_14017]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(contradiction,plain,
% 7.64/1.50      ( $false ),
% 7.64/1.50      inference(minisat,[status(thm)],[c_16104,c_14018,c_1607]) ).
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  ------                               Statistics
% 7.64/1.50  
% 7.64/1.50  ------ Selected
% 7.64/1.50  
% 7.64/1.50  total_time:                             0.537
% 7.64/1.50  
%------------------------------------------------------------------------------
