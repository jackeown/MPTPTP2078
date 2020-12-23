%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:30 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 206 expanded)
%              Number of clauses        :   55 (  67 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  252 ( 766 expanded)
%              Number of equality atoms :   75 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(k2_tops_1(X0,sK1),X0)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_538,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_539,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_563,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_539,c_0])).

cnf(c_971,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_538,c_563])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | X1 != X2
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_15])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_536,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_658,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_538,c_536])).

cnf(c_1161,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_971,c_658])).

cnf(c_11,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_207,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) != k2_tops_1(sK0,sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_208,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_212,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_208,c_16,c_15])).

cnf(c_7,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_233,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_234,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_236,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_15,c_14])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X0
    | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1)
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_236])).

cnf(c_247,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_537,plain,
    ( k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_1286,plain,
    ( k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1161,c_537])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_542,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_542,c_0])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_540,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_953,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_548,c_540])).

cnf(c_1870,plain,
    ( k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1286,c_953])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_535,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_638,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_538,c_535])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_543,plain,
    ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_882,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_538,c_543])).

cnf(c_1871,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1870,c_638,c_882])).

cnf(c_1872,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1871])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_716,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_717,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1872,c_717,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.59/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.07  
% 1.59/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.59/1.07  
% 1.59/1.07  ------  iProver source info
% 1.59/1.07  
% 1.59/1.07  git: date: 2020-06-30 10:37:57 +0100
% 1.59/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.59/1.07  git: non_committed_changes: false
% 1.59/1.07  git: last_make_outside_of_git: false
% 1.59/1.07  
% 1.59/1.07  ------ 
% 1.59/1.07  
% 1.59/1.07  ------ Input Options
% 1.59/1.07  
% 1.59/1.07  --out_options                           all
% 1.59/1.07  --tptp_safe_out                         true
% 1.59/1.07  --problem_path                          ""
% 1.59/1.07  --include_path                          ""
% 1.59/1.07  --clausifier                            res/vclausify_rel
% 1.59/1.07  --clausifier_options                    --mode clausify
% 1.59/1.07  --stdin                                 false
% 1.59/1.07  --stats_out                             all
% 1.59/1.07  
% 1.59/1.07  ------ General Options
% 1.59/1.07  
% 1.59/1.07  --fof                                   false
% 1.59/1.07  --time_out_real                         305.
% 1.59/1.07  --time_out_virtual                      -1.
% 1.59/1.07  --symbol_type_check                     false
% 1.59/1.07  --clausify_out                          false
% 1.59/1.07  --sig_cnt_out                           false
% 1.59/1.07  --trig_cnt_out                          false
% 1.59/1.07  --trig_cnt_out_tolerance                1.
% 1.59/1.07  --trig_cnt_out_sk_spl                   false
% 1.59/1.07  --abstr_cl_out                          false
% 1.59/1.07  
% 1.59/1.07  ------ Global Options
% 1.59/1.07  
% 1.59/1.07  --schedule                              default
% 1.59/1.07  --add_important_lit                     false
% 1.59/1.07  --prop_solver_per_cl                    1000
% 1.59/1.07  --min_unsat_core                        false
% 1.59/1.07  --soft_assumptions                      false
% 1.59/1.07  --soft_lemma_size                       3
% 1.59/1.07  --prop_impl_unit_size                   0
% 1.59/1.07  --prop_impl_unit                        []
% 1.59/1.07  --share_sel_clauses                     true
% 1.59/1.07  --reset_solvers                         false
% 1.59/1.07  --bc_imp_inh                            [conj_cone]
% 1.59/1.07  --conj_cone_tolerance                   3.
% 1.59/1.07  --extra_neg_conj                        none
% 1.59/1.07  --large_theory_mode                     true
% 1.59/1.07  --prolific_symb_bound                   200
% 1.59/1.07  --lt_threshold                          2000
% 1.59/1.07  --clause_weak_htbl                      true
% 1.59/1.07  --gc_record_bc_elim                     false
% 1.59/1.07  
% 1.59/1.07  ------ Preprocessing Options
% 1.59/1.07  
% 1.59/1.07  --preprocessing_flag                    true
% 1.59/1.07  --time_out_prep_mult                    0.1
% 1.59/1.07  --splitting_mode                        input
% 1.59/1.07  --splitting_grd                         true
% 1.59/1.07  --splitting_cvd                         false
% 1.59/1.07  --splitting_cvd_svl                     false
% 1.59/1.07  --splitting_nvd                         32
% 1.59/1.07  --sub_typing                            true
% 1.59/1.07  --prep_gs_sim                           true
% 1.59/1.07  --prep_unflatten                        true
% 1.59/1.07  --prep_res_sim                          true
% 1.59/1.07  --prep_upred                            true
% 1.59/1.07  --prep_sem_filter                       exhaustive
% 1.59/1.07  --prep_sem_filter_out                   false
% 1.59/1.07  --pred_elim                             true
% 1.59/1.07  --res_sim_input                         true
% 1.59/1.07  --eq_ax_congr_red                       true
% 1.59/1.07  --pure_diseq_elim                       true
% 1.59/1.07  --brand_transform                       false
% 1.59/1.07  --non_eq_to_eq                          false
% 1.59/1.07  --prep_def_merge                        true
% 1.59/1.07  --prep_def_merge_prop_impl              false
% 1.59/1.07  --prep_def_merge_mbd                    true
% 1.59/1.07  --prep_def_merge_tr_red                 false
% 1.59/1.07  --prep_def_merge_tr_cl                  false
% 1.59/1.07  --smt_preprocessing                     true
% 1.59/1.07  --smt_ac_axioms                         fast
% 1.59/1.07  --preprocessed_out                      false
% 1.59/1.07  --preprocessed_stats                    false
% 1.59/1.07  
% 1.59/1.07  ------ Abstraction refinement Options
% 1.59/1.07  
% 1.59/1.07  --abstr_ref                             []
% 1.59/1.07  --abstr_ref_prep                        false
% 1.59/1.07  --abstr_ref_until_sat                   false
% 1.59/1.07  --abstr_ref_sig_restrict                funpre
% 1.59/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/1.07  --abstr_ref_under                       []
% 1.59/1.07  
% 1.59/1.07  ------ SAT Options
% 1.59/1.07  
% 1.59/1.07  --sat_mode                              false
% 1.59/1.07  --sat_fm_restart_options                ""
% 1.59/1.07  --sat_gr_def                            false
% 1.59/1.07  --sat_epr_types                         true
% 1.59/1.07  --sat_non_cyclic_types                  false
% 1.59/1.07  --sat_finite_models                     false
% 1.59/1.07  --sat_fm_lemmas                         false
% 1.59/1.07  --sat_fm_prep                           false
% 1.59/1.07  --sat_fm_uc_incr                        true
% 1.59/1.07  --sat_out_model                         small
% 1.59/1.07  --sat_out_clauses                       false
% 1.59/1.07  
% 1.59/1.07  ------ QBF Options
% 1.59/1.07  
% 1.59/1.07  --qbf_mode                              false
% 1.59/1.07  --qbf_elim_univ                         false
% 1.59/1.07  --qbf_dom_inst                          none
% 1.59/1.07  --qbf_dom_pre_inst                      false
% 1.59/1.07  --qbf_sk_in                             false
% 1.59/1.07  --qbf_pred_elim                         true
% 1.59/1.07  --qbf_split                             512
% 1.59/1.07  
% 1.59/1.07  ------ BMC1 Options
% 1.59/1.07  
% 1.59/1.07  --bmc1_incremental                      false
% 1.59/1.07  --bmc1_axioms                           reachable_all
% 1.59/1.07  --bmc1_min_bound                        0
% 1.59/1.07  --bmc1_max_bound                        -1
% 1.59/1.07  --bmc1_max_bound_default                -1
% 1.59/1.07  --bmc1_symbol_reachability              true
% 1.59/1.07  --bmc1_property_lemmas                  false
% 1.59/1.07  --bmc1_k_induction                      false
% 1.59/1.07  --bmc1_non_equiv_states                 false
% 1.59/1.07  --bmc1_deadlock                         false
% 1.59/1.07  --bmc1_ucm                              false
% 1.59/1.07  --bmc1_add_unsat_core                   none
% 1.59/1.07  --bmc1_unsat_core_children              false
% 1.59/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/1.07  --bmc1_out_stat                         full
% 1.59/1.07  --bmc1_ground_init                      false
% 1.59/1.07  --bmc1_pre_inst_next_state              false
% 1.59/1.07  --bmc1_pre_inst_state                   false
% 1.59/1.07  --bmc1_pre_inst_reach_state             false
% 1.59/1.07  --bmc1_out_unsat_core                   false
% 1.59/1.07  --bmc1_aig_witness_out                  false
% 1.59/1.07  --bmc1_verbose                          false
% 1.59/1.07  --bmc1_dump_clauses_tptp                false
% 1.59/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.59/1.07  --bmc1_dump_file                        -
% 1.59/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.59/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.59/1.07  --bmc1_ucm_extend_mode                  1
% 1.59/1.07  --bmc1_ucm_init_mode                    2
% 1.59/1.07  --bmc1_ucm_cone_mode                    none
% 1.59/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.59/1.07  --bmc1_ucm_relax_model                  4
% 1.59/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.59/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/1.07  --bmc1_ucm_layered_model                none
% 1.59/1.07  --bmc1_ucm_max_lemma_size               10
% 1.59/1.07  
% 1.59/1.07  ------ AIG Options
% 1.59/1.07  
% 1.59/1.07  --aig_mode                              false
% 1.59/1.07  
% 1.59/1.07  ------ Instantiation Options
% 1.59/1.07  
% 1.59/1.07  --instantiation_flag                    true
% 1.59/1.07  --inst_sos_flag                         false
% 1.59/1.07  --inst_sos_phase                        true
% 1.59/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/1.07  --inst_lit_sel_side                     num_symb
% 1.59/1.07  --inst_solver_per_active                1400
% 1.59/1.07  --inst_solver_calls_frac                1.
% 1.59/1.07  --inst_passive_queue_type               priority_queues
% 1.59/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/1.07  --inst_passive_queues_freq              [25;2]
% 1.59/1.07  --inst_dismatching                      true
% 1.59/1.07  --inst_eager_unprocessed_to_passive     true
% 1.59/1.07  --inst_prop_sim_given                   true
% 1.59/1.07  --inst_prop_sim_new                     false
% 1.59/1.07  --inst_subs_new                         false
% 1.59/1.07  --inst_eq_res_simp                      false
% 1.59/1.07  --inst_subs_given                       false
% 1.59/1.07  --inst_orphan_elimination               true
% 1.59/1.07  --inst_learning_loop_flag               true
% 1.59/1.07  --inst_learning_start                   3000
% 1.59/1.07  --inst_learning_factor                  2
% 1.59/1.07  --inst_start_prop_sim_after_learn       3
% 1.59/1.07  --inst_sel_renew                        solver
% 1.59/1.07  --inst_lit_activity_flag                true
% 1.59/1.07  --inst_restr_to_given                   false
% 1.59/1.07  --inst_activity_threshold               500
% 1.59/1.07  --inst_out_proof                        true
% 1.59/1.07  
% 1.59/1.07  ------ Resolution Options
% 1.59/1.07  
% 1.59/1.07  --resolution_flag                       true
% 1.59/1.07  --res_lit_sel                           adaptive
% 1.59/1.07  --res_lit_sel_side                      none
% 1.59/1.07  --res_ordering                          kbo
% 1.59/1.07  --res_to_prop_solver                    active
% 1.59/1.07  --res_prop_simpl_new                    false
% 1.59/1.07  --res_prop_simpl_given                  true
% 1.59/1.07  --res_passive_queue_type                priority_queues
% 1.59/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/1.07  --res_passive_queues_freq               [15;5]
% 1.59/1.07  --res_forward_subs                      full
% 1.59/1.07  --res_backward_subs                     full
% 1.59/1.07  --res_forward_subs_resolution           true
% 1.59/1.07  --res_backward_subs_resolution          true
% 1.59/1.07  --res_orphan_elimination                true
% 1.59/1.07  --res_time_limit                        2.
% 1.59/1.07  --res_out_proof                         true
% 1.59/1.07  
% 1.59/1.07  ------ Superposition Options
% 1.59/1.07  
% 1.59/1.07  --superposition_flag                    true
% 1.59/1.07  --sup_passive_queue_type                priority_queues
% 1.59/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.59/1.07  --demod_completeness_check              fast
% 1.59/1.07  --demod_use_ground                      true
% 1.59/1.07  --sup_to_prop_solver                    passive
% 1.59/1.07  --sup_prop_simpl_new                    true
% 1.59/1.07  --sup_prop_simpl_given                  true
% 1.59/1.07  --sup_fun_splitting                     false
% 1.59/1.07  --sup_smt_interval                      50000
% 1.59/1.07  
% 1.59/1.07  ------ Superposition Simplification Setup
% 1.59/1.07  
% 1.59/1.07  --sup_indices_passive                   []
% 1.59/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.07  --sup_full_bw                           [BwDemod]
% 1.59/1.07  --sup_immed_triv                        [TrivRules]
% 1.59/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.07  --sup_immed_bw_main                     []
% 1.59/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.07  
% 1.59/1.07  ------ Combination Options
% 1.59/1.07  
% 1.59/1.07  --comb_res_mult                         3
% 1.59/1.07  --comb_sup_mult                         2
% 1.59/1.07  --comb_inst_mult                        10
% 1.59/1.07  
% 1.59/1.07  ------ Debug Options
% 1.59/1.07  
% 1.59/1.07  --dbg_backtrace                         false
% 1.59/1.07  --dbg_dump_prop_clauses                 false
% 1.59/1.07  --dbg_dump_prop_clauses_file            -
% 1.59/1.07  --dbg_out_stat                          false
% 1.59/1.07  ------ Parsing...
% 1.59/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.59/1.07  
% 1.59/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.59/1.07  
% 1.59/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.59/1.07  
% 1.59/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.59/1.07  ------ Proving...
% 1.59/1.07  ------ Problem Properties 
% 1.59/1.07  
% 1.59/1.07  
% 1.59/1.07  clauses                                 10
% 1.59/1.07  conjectures                             1
% 1.59/1.08  EPR                                     0
% 1.59/1.08  Horn                                    10
% 1.59/1.08  unary                                   3
% 1.59/1.08  binary                                  7
% 1.59/1.08  lits                                    17
% 1.59/1.08  lits eq                                 7
% 1.59/1.08  fd_pure                                 0
% 1.59/1.08  fd_pseudo                               0
% 1.59/1.08  fd_cond                                 0
% 1.59/1.08  fd_pseudo_cond                          0
% 1.59/1.08  AC symbols                              0
% 1.59/1.08  
% 1.59/1.08  ------ Schedule dynamic 5 is on 
% 1.59/1.08  
% 1.59/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  ------ 
% 1.59/1.08  Current options:
% 1.59/1.08  ------ 
% 1.59/1.08  
% 1.59/1.08  ------ Input Options
% 1.59/1.08  
% 1.59/1.08  --out_options                           all
% 1.59/1.08  --tptp_safe_out                         true
% 1.59/1.08  --problem_path                          ""
% 1.59/1.08  --include_path                          ""
% 1.59/1.08  --clausifier                            res/vclausify_rel
% 1.59/1.08  --clausifier_options                    --mode clausify
% 1.59/1.08  --stdin                                 false
% 1.59/1.08  --stats_out                             all
% 1.59/1.08  
% 1.59/1.08  ------ General Options
% 1.59/1.08  
% 1.59/1.08  --fof                                   false
% 1.59/1.08  --time_out_real                         305.
% 1.59/1.08  --time_out_virtual                      -1.
% 1.59/1.08  --symbol_type_check                     false
% 1.59/1.08  --clausify_out                          false
% 1.59/1.08  --sig_cnt_out                           false
% 1.59/1.08  --trig_cnt_out                          false
% 1.59/1.08  --trig_cnt_out_tolerance                1.
% 1.59/1.08  --trig_cnt_out_sk_spl                   false
% 1.59/1.08  --abstr_cl_out                          false
% 1.59/1.08  
% 1.59/1.08  ------ Global Options
% 1.59/1.08  
% 1.59/1.08  --schedule                              default
% 1.59/1.08  --add_important_lit                     false
% 1.59/1.08  --prop_solver_per_cl                    1000
% 1.59/1.08  --min_unsat_core                        false
% 1.59/1.08  --soft_assumptions                      false
% 1.59/1.08  --soft_lemma_size                       3
% 1.59/1.08  --prop_impl_unit_size                   0
% 1.59/1.08  --prop_impl_unit                        []
% 1.59/1.08  --share_sel_clauses                     true
% 1.59/1.08  --reset_solvers                         false
% 1.59/1.08  --bc_imp_inh                            [conj_cone]
% 1.59/1.08  --conj_cone_tolerance                   3.
% 1.59/1.08  --extra_neg_conj                        none
% 1.59/1.08  --large_theory_mode                     true
% 1.59/1.08  --prolific_symb_bound                   200
% 1.59/1.08  --lt_threshold                          2000
% 1.59/1.08  --clause_weak_htbl                      true
% 1.59/1.08  --gc_record_bc_elim                     false
% 1.59/1.08  
% 1.59/1.08  ------ Preprocessing Options
% 1.59/1.08  
% 1.59/1.08  --preprocessing_flag                    true
% 1.59/1.08  --time_out_prep_mult                    0.1
% 1.59/1.08  --splitting_mode                        input
% 1.59/1.08  --splitting_grd                         true
% 1.59/1.08  --splitting_cvd                         false
% 1.59/1.08  --splitting_cvd_svl                     false
% 1.59/1.08  --splitting_nvd                         32
% 1.59/1.08  --sub_typing                            true
% 1.59/1.08  --prep_gs_sim                           true
% 1.59/1.08  --prep_unflatten                        true
% 1.59/1.08  --prep_res_sim                          true
% 1.59/1.08  --prep_upred                            true
% 1.59/1.08  --prep_sem_filter                       exhaustive
% 1.59/1.08  --prep_sem_filter_out                   false
% 1.59/1.08  --pred_elim                             true
% 1.59/1.08  --res_sim_input                         true
% 1.59/1.08  --eq_ax_congr_red                       true
% 1.59/1.08  --pure_diseq_elim                       true
% 1.59/1.08  --brand_transform                       false
% 1.59/1.08  --non_eq_to_eq                          false
% 1.59/1.08  --prep_def_merge                        true
% 1.59/1.08  --prep_def_merge_prop_impl              false
% 1.59/1.08  --prep_def_merge_mbd                    true
% 1.59/1.08  --prep_def_merge_tr_red                 false
% 1.59/1.08  --prep_def_merge_tr_cl                  false
% 1.59/1.08  --smt_preprocessing                     true
% 1.59/1.08  --smt_ac_axioms                         fast
% 1.59/1.08  --preprocessed_out                      false
% 1.59/1.08  --preprocessed_stats                    false
% 1.59/1.08  
% 1.59/1.08  ------ Abstraction refinement Options
% 1.59/1.08  
% 1.59/1.08  --abstr_ref                             []
% 1.59/1.08  --abstr_ref_prep                        false
% 1.59/1.08  --abstr_ref_until_sat                   false
% 1.59/1.08  --abstr_ref_sig_restrict                funpre
% 1.59/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/1.08  --abstr_ref_under                       []
% 1.59/1.08  
% 1.59/1.08  ------ SAT Options
% 1.59/1.08  
% 1.59/1.08  --sat_mode                              false
% 1.59/1.08  --sat_fm_restart_options                ""
% 1.59/1.08  --sat_gr_def                            false
% 1.59/1.08  --sat_epr_types                         true
% 1.59/1.08  --sat_non_cyclic_types                  false
% 1.59/1.08  --sat_finite_models                     false
% 1.59/1.08  --sat_fm_lemmas                         false
% 1.59/1.08  --sat_fm_prep                           false
% 1.59/1.08  --sat_fm_uc_incr                        true
% 1.59/1.08  --sat_out_model                         small
% 1.59/1.08  --sat_out_clauses                       false
% 1.59/1.08  
% 1.59/1.08  ------ QBF Options
% 1.59/1.08  
% 1.59/1.08  --qbf_mode                              false
% 1.59/1.08  --qbf_elim_univ                         false
% 1.59/1.08  --qbf_dom_inst                          none
% 1.59/1.08  --qbf_dom_pre_inst                      false
% 1.59/1.08  --qbf_sk_in                             false
% 1.59/1.08  --qbf_pred_elim                         true
% 1.59/1.08  --qbf_split                             512
% 1.59/1.08  
% 1.59/1.08  ------ BMC1 Options
% 1.59/1.08  
% 1.59/1.08  --bmc1_incremental                      false
% 1.59/1.08  --bmc1_axioms                           reachable_all
% 1.59/1.08  --bmc1_min_bound                        0
% 1.59/1.08  --bmc1_max_bound                        -1
% 1.59/1.08  --bmc1_max_bound_default                -1
% 1.59/1.08  --bmc1_symbol_reachability              true
% 1.59/1.08  --bmc1_property_lemmas                  false
% 1.59/1.08  --bmc1_k_induction                      false
% 1.59/1.08  --bmc1_non_equiv_states                 false
% 1.59/1.08  --bmc1_deadlock                         false
% 1.59/1.08  --bmc1_ucm                              false
% 1.59/1.08  --bmc1_add_unsat_core                   none
% 1.59/1.08  --bmc1_unsat_core_children              false
% 1.59/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/1.08  --bmc1_out_stat                         full
% 1.59/1.08  --bmc1_ground_init                      false
% 1.59/1.08  --bmc1_pre_inst_next_state              false
% 1.59/1.08  --bmc1_pre_inst_state                   false
% 1.59/1.08  --bmc1_pre_inst_reach_state             false
% 1.59/1.08  --bmc1_out_unsat_core                   false
% 1.59/1.08  --bmc1_aig_witness_out                  false
% 1.59/1.08  --bmc1_verbose                          false
% 1.59/1.08  --bmc1_dump_clauses_tptp                false
% 1.59/1.08  --bmc1_dump_unsat_core_tptp             false
% 1.59/1.08  --bmc1_dump_file                        -
% 1.59/1.08  --bmc1_ucm_expand_uc_limit              128
% 1.59/1.08  --bmc1_ucm_n_expand_iterations          6
% 1.59/1.08  --bmc1_ucm_extend_mode                  1
% 1.59/1.08  --bmc1_ucm_init_mode                    2
% 1.59/1.08  --bmc1_ucm_cone_mode                    none
% 1.59/1.08  --bmc1_ucm_reduced_relation_type        0
% 1.59/1.08  --bmc1_ucm_relax_model                  4
% 1.59/1.08  --bmc1_ucm_full_tr_after_sat            true
% 1.59/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/1.08  --bmc1_ucm_layered_model                none
% 1.59/1.08  --bmc1_ucm_max_lemma_size               10
% 1.59/1.08  
% 1.59/1.08  ------ AIG Options
% 1.59/1.08  
% 1.59/1.08  --aig_mode                              false
% 1.59/1.08  
% 1.59/1.08  ------ Instantiation Options
% 1.59/1.08  
% 1.59/1.08  --instantiation_flag                    true
% 1.59/1.08  --inst_sos_flag                         false
% 1.59/1.08  --inst_sos_phase                        true
% 1.59/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/1.08  --inst_lit_sel_side                     none
% 1.59/1.08  --inst_solver_per_active                1400
% 1.59/1.08  --inst_solver_calls_frac                1.
% 1.59/1.08  --inst_passive_queue_type               priority_queues
% 1.59/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/1.08  --inst_passive_queues_freq              [25;2]
% 1.59/1.08  --inst_dismatching                      true
% 1.59/1.08  --inst_eager_unprocessed_to_passive     true
% 1.59/1.08  --inst_prop_sim_given                   true
% 1.59/1.08  --inst_prop_sim_new                     false
% 1.59/1.08  --inst_subs_new                         false
% 1.59/1.08  --inst_eq_res_simp                      false
% 1.59/1.08  --inst_subs_given                       false
% 1.59/1.08  --inst_orphan_elimination               true
% 1.59/1.08  --inst_learning_loop_flag               true
% 1.59/1.08  --inst_learning_start                   3000
% 1.59/1.08  --inst_learning_factor                  2
% 1.59/1.08  --inst_start_prop_sim_after_learn       3
% 1.59/1.08  --inst_sel_renew                        solver
% 1.59/1.08  --inst_lit_activity_flag                true
% 1.59/1.08  --inst_restr_to_given                   false
% 1.59/1.08  --inst_activity_threshold               500
% 1.59/1.08  --inst_out_proof                        true
% 1.59/1.08  
% 1.59/1.08  ------ Resolution Options
% 1.59/1.08  
% 1.59/1.08  --resolution_flag                       false
% 1.59/1.08  --res_lit_sel                           adaptive
% 1.59/1.08  --res_lit_sel_side                      none
% 1.59/1.08  --res_ordering                          kbo
% 1.59/1.08  --res_to_prop_solver                    active
% 1.59/1.08  --res_prop_simpl_new                    false
% 1.59/1.08  --res_prop_simpl_given                  true
% 1.59/1.08  --res_passive_queue_type                priority_queues
% 1.59/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/1.08  --res_passive_queues_freq               [15;5]
% 1.59/1.08  --res_forward_subs                      full
% 1.59/1.08  --res_backward_subs                     full
% 1.59/1.08  --res_forward_subs_resolution           true
% 1.59/1.08  --res_backward_subs_resolution          true
% 1.59/1.08  --res_orphan_elimination                true
% 1.59/1.08  --res_time_limit                        2.
% 1.59/1.08  --res_out_proof                         true
% 1.59/1.08  
% 1.59/1.08  ------ Superposition Options
% 1.59/1.08  
% 1.59/1.08  --superposition_flag                    true
% 1.59/1.08  --sup_passive_queue_type                priority_queues
% 1.59/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/1.08  --sup_passive_queues_freq               [8;1;4]
% 1.59/1.08  --demod_completeness_check              fast
% 1.59/1.08  --demod_use_ground                      true
% 1.59/1.08  --sup_to_prop_solver                    passive
% 1.59/1.08  --sup_prop_simpl_new                    true
% 1.59/1.08  --sup_prop_simpl_given                  true
% 1.59/1.08  --sup_fun_splitting                     false
% 1.59/1.08  --sup_smt_interval                      50000
% 1.59/1.08  
% 1.59/1.08  ------ Superposition Simplification Setup
% 1.59/1.08  
% 1.59/1.08  --sup_indices_passive                   []
% 1.59/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.08  --sup_full_bw                           [BwDemod]
% 1.59/1.08  --sup_immed_triv                        [TrivRules]
% 1.59/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.08  --sup_immed_bw_main                     []
% 1.59/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.08  
% 1.59/1.08  ------ Combination Options
% 1.59/1.08  
% 1.59/1.08  --comb_res_mult                         3
% 1.59/1.08  --comb_sup_mult                         2
% 1.59/1.08  --comb_inst_mult                        10
% 1.59/1.08  
% 1.59/1.08  ------ Debug Options
% 1.59/1.08  
% 1.59/1.08  --dbg_backtrace                         false
% 1.59/1.08  --dbg_dump_prop_clauses                 false
% 1.59/1.08  --dbg_dump_prop_clauses_file            -
% 1.59/1.08  --dbg_out_stat                          false
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  ------ Proving...
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  % SZS status Theorem for theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  fof(f12,conjecture,(
% 1.59/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f13,negated_conjecture,(
% 1.59/1.08    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 1.59/1.08    inference(negated_conjecture,[],[f12])).
% 1.59/1.08  
% 1.59/1.08  fof(f24,plain,(
% 1.59/1.08    ? [X0] : (? [X1] : ((~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f13])).
% 1.59/1.08  
% 1.59/1.08  fof(f25,plain,(
% 1.59/1.08    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.59/1.08    inference(flattening,[],[f24])).
% 1.59/1.08  
% 1.59/1.08  fof(f28,plain,(
% 1.59/1.08    ( ! [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tops_1(k2_tops_1(X0,sK1),X0) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.59/1.08    introduced(choice_axiom,[])).
% 1.59/1.08  
% 1.59/1.08  fof(f27,plain,(
% 1.59/1.08    ? [X0] : (? [X1] : (~v3_tops_1(k2_tops_1(X0,X1),X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v3_tops_1(k2_tops_1(sK0,X1),sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.59/1.08    introduced(choice_axiom,[])).
% 1.59/1.08  
% 1.59/1.08  fof(f29,plain,(
% 1.59/1.08    (~v3_tops_1(k2_tops_1(sK0,sK1),sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.59/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).
% 1.59/1.08  
% 1.59/1.08  fof(f44,plain,(
% 1.59/1.08    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/1.08    inference(cnf_transformation,[],[f29])).
% 1.59/1.08  
% 1.59/1.08  fof(f6,axiom,(
% 1.59/1.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f17,plain,(
% 1.59/1.08    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f6])).
% 1.59/1.08  
% 1.59/1.08  fof(f35,plain,(
% 1.59/1.08    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/1.08    inference(cnf_transformation,[],[f17])).
% 1.59/1.08  
% 1.59/1.08  fof(f1,axiom,(
% 1.59/1.08    ! [X0] : k2_subset_1(X0) = X0),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f30,plain,(
% 1.59/1.08    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.59/1.08    inference(cnf_transformation,[],[f1])).
% 1.59/1.08  
% 1.59/1.08  fof(f8,axiom,(
% 1.59/1.08    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f19,plain,(
% 1.59/1.08    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.59/1.08    inference(ennf_transformation,[],[f8])).
% 1.59/1.08  
% 1.59/1.08  fof(f38,plain,(
% 1.59/1.08    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.59/1.08    inference(cnf_transformation,[],[f19])).
% 1.59/1.08  
% 1.59/1.08  fof(f9,axiom,(
% 1.59/1.08    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f20,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.59/1.08    inference(ennf_transformation,[],[f9])).
% 1.59/1.08  
% 1.59/1.08  fof(f39,plain,(
% 1.59/1.08    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.59/1.08    inference(cnf_transformation,[],[f20])).
% 1.59/1.08  
% 1.59/1.08  fof(f43,plain,(
% 1.59/1.08    l1_pre_topc(sK0)),
% 1.59/1.08    inference(cnf_transformation,[],[f29])).
% 1.59/1.08  
% 1.59/1.08  fof(f11,axiom,(
% 1.59/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f22,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f11])).
% 1.59/1.08  
% 1.59/1.08  fof(f23,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/1.08    inference(flattening,[],[f22])).
% 1.59/1.08  
% 1.59/1.08  fof(f41,plain,(
% 1.59/1.08    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/1.08    inference(cnf_transformation,[],[f23])).
% 1.59/1.08  
% 1.59/1.08  fof(f46,plain,(
% 1.59/1.08    ~v3_tops_1(k2_tops_1(sK0,sK1),sK0)),
% 1.59/1.08    inference(cnf_transformation,[],[f29])).
% 1.59/1.08  
% 1.59/1.08  fof(f42,plain,(
% 1.59/1.08    v2_pre_topc(sK0)),
% 1.59/1.08    inference(cnf_transformation,[],[f29])).
% 1.59/1.08  
% 1.59/1.08  fof(f7,axiom,(
% 1.59/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f18,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.08    inference(ennf_transformation,[],[f7])).
% 1.59/1.08  
% 1.59/1.08  fof(f26,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.08    inference(nnf_transformation,[],[f18])).
% 1.59/1.08  
% 1.59/1.08  fof(f36,plain,(
% 1.59/1.08    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/1.08    inference(cnf_transformation,[],[f26])).
% 1.59/1.08  
% 1.59/1.08  fof(f45,plain,(
% 1.59/1.08    v4_pre_topc(sK1,sK0)),
% 1.59/1.08    inference(cnf_transformation,[],[f29])).
% 1.59/1.08  
% 1.59/1.08  fof(f3,axiom,(
% 1.59/1.08    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f32,plain,(
% 1.59/1.08    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.59/1.08    inference(cnf_transformation,[],[f3])).
% 1.59/1.08  
% 1.59/1.08  fof(f5,axiom,(
% 1.59/1.08    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f16,plain,(
% 1.59/1.08    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f5])).
% 1.59/1.08  
% 1.59/1.08  fof(f34,plain,(
% 1.59/1.08    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/1.08    inference(cnf_transformation,[],[f16])).
% 1.59/1.08  
% 1.59/1.08  fof(f10,axiom,(
% 1.59/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f21,plain,(
% 1.59/1.08    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.08    inference(ennf_transformation,[],[f10])).
% 1.59/1.08  
% 1.59/1.08  fof(f40,plain,(
% 1.59/1.08    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/1.08    inference(cnf_transformation,[],[f21])).
% 1.59/1.08  
% 1.59/1.08  fof(f2,axiom,(
% 1.59/1.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f14,plain,(
% 1.59/1.08    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f2])).
% 1.59/1.08  
% 1.59/1.08  fof(f31,plain,(
% 1.59/1.08    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/1.08    inference(cnf_transformation,[],[f14])).
% 1.59/1.08  
% 1.59/1.08  fof(f4,axiom,(
% 1.59/1.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.59/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.59/1.08  
% 1.59/1.08  fof(f15,plain,(
% 1.59/1.08    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/1.08    inference(ennf_transformation,[],[f4])).
% 1.59/1.08  
% 1.59/1.08  fof(f33,plain,(
% 1.59/1.08    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/1.08    inference(cnf_transformation,[],[f15])).
% 1.59/1.08  
% 1.59/1.08  cnf(c_14,negated_conjecture,
% 1.59/1.08      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.59/1.08      inference(cnf_transformation,[],[f44]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_538,plain,
% 1.59/1.08      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_5,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.59/1.08      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 1.59/1.08      inference(cnf_transformation,[],[f35]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_539,plain,
% 1.59/1.08      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 1.59/1.08      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_0,plain,
% 1.59/1.08      ( k2_subset_1(X0) = X0 ),
% 1.59/1.08      inference(cnf_transformation,[],[f30]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_563,plain,
% 1.59/1.08      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 1.59/1.08      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.59/1.08      inference(light_normalisation,[status(thm)],[c_539,c_0]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_971,plain,
% 1.59/1.08      ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 1.59/1.08      inference(superposition,[status(thm)],[c_538,c_563]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_8,plain,
% 1.59/1.08      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f38]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_9,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | ~ l1_struct_0(X1)
% 1.59/1.08      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 1.59/1.08      inference(cnf_transformation,[],[f39]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_188,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | ~ l1_pre_topc(X2)
% 1.59/1.08      | X1 != X2
% 1.59/1.08      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_189,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | ~ l1_pre_topc(X1)
% 1.59/1.08      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_188]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_15,negated_conjecture,
% 1.59/1.08      ( l1_pre_topc(sK0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f43]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_259,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 1.59/1.08      | sK0 != X1 ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_189,c_15]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_260,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_259]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_536,plain,
% 1.59/1.08      ( k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 1.59/1.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_658,plain,
% 1.59/1.08      ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 1.59/1.08      inference(superposition,[status(thm)],[c_538,c_536]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1161,plain,
% 1.59/1.08      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.59/1.08      inference(demodulation,[status(thm)],[c_971,c_658]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_11,plain,
% 1.59/1.08      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 1.59/1.08      | ~ v3_pre_topc(X1,X0)
% 1.59/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.08      | ~ v2_pre_topc(X0)
% 1.59/1.08      | ~ l1_pre_topc(X0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f41]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_12,negated_conjecture,
% 1.59/1.08      ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f46]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_207,plain,
% 1.59/1.08      ( ~ v3_pre_topc(X0,X1)
% 1.59/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | ~ v2_pre_topc(X1)
% 1.59/1.08      | ~ l1_pre_topc(X1)
% 1.59/1.08      | k2_tops_1(X1,X0) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | sK0 != X1 ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_208,plain,
% 1.59/1.08      ( ~ v3_pre_topc(X0,sK0)
% 1.59/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | ~ v2_pre_topc(sK0)
% 1.59/1.08      | ~ l1_pre_topc(sK0)
% 1.59/1.08      | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_207]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_16,negated_conjecture,
% 1.59/1.08      ( v2_pre_topc(sK0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f42]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_212,plain,
% 1.59/1.08      ( ~ v3_pre_topc(X0,sK0)
% 1.59/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1) ),
% 1.59/1.08      inference(global_propositional_subsumption,
% 1.59/1.08                [status(thm)],
% 1.59/1.08                [c_208,c_16,c_15]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_7,plain,
% 1.59/1.08      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.59/1.08      | ~ v4_pre_topc(X1,X0)
% 1.59/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.08      | ~ l1_pre_topc(X0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f36]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_13,negated_conjecture,
% 1.59/1.08      ( v4_pre_topc(sK1,sK0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f45]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_233,plain,
% 1.59/1.08      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.59/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.08      | ~ l1_pre_topc(X0)
% 1.59/1.08      | sK1 != X1
% 1.59/1.08      | sK0 != X0 ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_234,plain,
% 1.59/1.08      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
% 1.59/1.08      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | ~ l1_pre_topc(sK0) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_233]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_236,plain,
% 1.59/1.08      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
% 1.59/1.08      inference(global_propositional_subsumption,
% 1.59/1.08                [status(thm)],
% 1.59/1.08                [c_234,c_15,c_14]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_246,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X0
% 1.59/1.08      | k2_tops_1(sK0,X0) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | sK0 != sK0 ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_212,c_236]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_247,plain,
% 1.59/1.08      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_246]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_537,plain,
% 1.59/1.08      ( k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1286,plain,
% 1.59/1.08      ( k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(demodulation,[status(thm)],[c_1161,c_537]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_2,plain,
% 1.59/1.08      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.59/1.08      inference(cnf_transformation,[],[f32]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_542,plain,
% 1.59/1.08      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_548,plain,
% 1.59/1.08      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.59/1.08      inference(light_normalisation,[status(thm)],[c_542,c_0]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_4,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.59/1.08      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.59/1.08      inference(cnf_transformation,[],[f34]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_540,plain,
% 1.59/1.08      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 1.59/1.08      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_953,plain,
% 1.59/1.08      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 1.59/1.08      inference(superposition,[status(thm)],[c_548,c_540]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1870,plain,
% 1.59/1.08      ( k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(demodulation,[status(thm)],[c_1286,c_953]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_10,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | ~ l1_pre_topc(X1)
% 1.59/1.08      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f40]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_271,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.08      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 1.59/1.08      | sK0 != X1 ),
% 1.59/1.08      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_272,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
% 1.59/1.08      inference(unflattening,[status(thm)],[c_271]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_535,plain,
% 1.59/1.08      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
% 1.59/1.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_638,plain,
% 1.59/1.08      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 1.59/1.08      inference(superposition,[status(thm)],[c_538,c_535]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.59/1.08      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 1.59/1.08      inference(cnf_transformation,[],[f31]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_543,plain,
% 1.59/1.08      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
% 1.59/1.08      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_882,plain,
% 1.59/1.08      ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 1.59/1.08      inference(superposition,[status(thm)],[c_538,c_543]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1871,plain,
% 1.59/1.08      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
% 1.59/1.08      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(light_normalisation,[status(thm)],[c_1870,c_638,c_882]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_1872,plain,
% 1.59/1.08      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(equality_resolution_simp,[status(thm)],[c_1871]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_3,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.59/1.08      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 1.59/1.08      inference(cnf_transformation,[],[f33]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_618,plain,
% 1.59/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.59/1.08      inference(instantiation,[status(thm)],[c_3]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_716,plain,
% 1.59/1.08      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.59/1.08      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.59/1.08      inference(instantiation,[status(thm)],[c_618]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_717,plain,
% 1.59/1.08      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.59/1.08      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(c_19,plain,
% 1.59/1.08      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.59/1.08      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.59/1.08  
% 1.59/1.08  cnf(contradiction,plain,
% 1.59/1.08      ( $false ),
% 1.59/1.08      inference(minisat,[status(thm)],[c_1872,c_717,c_19]) ).
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  ------                               Statistics
% 1.59/1.08  
% 1.59/1.08  ------ General
% 1.59/1.08  
% 1.59/1.08  abstr_ref_over_cycles:                  0
% 1.59/1.08  abstr_ref_under_cycles:                 0
% 1.59/1.08  gc_basic_clause_elim:                   0
% 1.59/1.08  forced_gc_time:                         0
% 1.59/1.08  parsing_time:                           0.012
% 1.59/1.08  unif_index_cands_time:                  0.
% 1.59/1.08  unif_index_add_time:                    0.
% 1.59/1.08  orderings_time:                         0.
% 1.59/1.08  out_proof_time:                         0.03
% 1.59/1.08  total_time:                             0.141
% 1.59/1.08  num_of_symbols:                         49
% 1.59/1.08  num_of_terms:                           1747
% 1.59/1.08  
% 1.59/1.08  ------ Preprocessing
% 1.59/1.08  
% 1.59/1.08  num_of_splits:                          0
% 1.59/1.08  num_of_split_atoms:                     0
% 1.59/1.08  num_of_reused_defs:                     0
% 1.59/1.08  num_eq_ax_congr_red:                    19
% 1.59/1.08  num_of_sem_filtered_clauses:            1
% 1.59/1.08  num_of_subtypes:                        0
% 1.59/1.08  monotx_restored_types:                  0
% 1.59/1.08  sat_num_of_epr_types:                   0
% 1.59/1.08  sat_num_of_non_cyclic_types:            0
% 1.59/1.08  sat_guarded_non_collapsed_types:        0
% 1.59/1.08  num_pure_diseq_elim:                    0
% 1.59/1.08  simp_replaced_by:                       0
% 1.59/1.08  res_preprocessed:                       68
% 1.59/1.08  prep_upred:                             0
% 1.59/1.08  prep_unflattend:                        7
% 1.59/1.08  smt_new_axioms:                         0
% 1.59/1.08  pred_elim_cands:                        1
% 1.59/1.08  pred_elim:                              6
% 1.59/1.08  pred_elim_cl:                           7
% 1.59/1.08  pred_elim_cycles:                       8
% 1.59/1.08  merged_defs:                            0
% 1.59/1.08  merged_defs_ncl:                        0
% 1.59/1.08  bin_hyper_res:                          0
% 1.59/1.08  prep_cycles:                            4
% 1.59/1.08  pred_elim_time:                         0.004
% 1.59/1.08  splitting_time:                         0.
% 1.59/1.08  sem_filter_time:                        0.
% 1.59/1.08  monotx_time:                            0.001
% 1.59/1.08  subtype_inf_time:                       0.
% 1.59/1.08  
% 1.59/1.08  ------ Problem properties
% 1.59/1.08  
% 1.59/1.08  clauses:                                10
% 1.59/1.08  conjectures:                            1
% 1.59/1.08  epr:                                    0
% 1.59/1.08  horn:                                   10
% 1.59/1.08  ground:                                 2
% 1.59/1.08  unary:                                  3
% 1.59/1.08  binary:                                 7
% 1.59/1.08  lits:                                   17
% 1.59/1.08  lits_eq:                                7
% 1.59/1.08  fd_pure:                                0
% 1.59/1.08  fd_pseudo:                              0
% 1.59/1.08  fd_cond:                                0
% 1.59/1.08  fd_pseudo_cond:                         0
% 1.59/1.08  ac_symbols:                             0
% 1.59/1.08  
% 1.59/1.08  ------ Propositional Solver
% 1.59/1.08  
% 1.59/1.08  prop_solver_calls:                      27
% 1.59/1.08  prop_fast_solver_calls:                 344
% 1.59/1.08  smt_solver_calls:                       0
% 1.59/1.08  smt_fast_solver_calls:                  0
% 1.59/1.08  prop_num_of_clauses:                    692
% 1.59/1.08  prop_preprocess_simplified:             2463
% 1.59/1.08  prop_fo_subsumed:                       4
% 1.59/1.08  prop_solver_time:                       0.
% 1.59/1.08  smt_solver_time:                        0.
% 1.59/1.08  smt_fast_solver_time:                   0.
% 1.59/1.08  prop_fast_solver_time:                  0.
% 1.59/1.08  prop_unsat_core_time:                   0.
% 1.59/1.08  
% 1.59/1.08  ------ QBF
% 1.59/1.08  
% 1.59/1.08  qbf_q_res:                              0
% 1.59/1.08  qbf_num_tautologies:                    0
% 1.59/1.08  qbf_prep_cycles:                        0
% 1.59/1.08  
% 1.59/1.08  ------ BMC1
% 1.59/1.08  
% 1.59/1.08  bmc1_current_bound:                     -1
% 1.59/1.08  bmc1_last_solved_bound:                 -1
% 1.59/1.08  bmc1_unsat_core_size:                   -1
% 1.59/1.08  bmc1_unsat_core_parents_size:           -1
% 1.59/1.08  bmc1_merge_next_fun:                    0
% 1.59/1.08  bmc1_unsat_core_clauses_time:           0.
% 1.59/1.08  
% 1.59/1.08  ------ Instantiation
% 1.59/1.08  
% 1.59/1.08  inst_num_of_clauses:                    238
% 1.59/1.08  inst_num_in_passive:                    34
% 1.59/1.08  inst_num_in_active:                     141
% 1.59/1.08  inst_num_in_unprocessed:                63
% 1.59/1.08  inst_num_of_loops:                      150
% 1.59/1.08  inst_num_of_learning_restarts:          0
% 1.59/1.08  inst_num_moves_active_passive:          6
% 1.59/1.08  inst_lit_activity:                      0
% 1.59/1.08  inst_lit_activity_moves:                0
% 1.59/1.08  inst_num_tautologies:                   0
% 1.59/1.08  inst_num_prop_implied:                  0
% 1.59/1.08  inst_num_existing_simplified:           0
% 1.59/1.08  inst_num_eq_res_simplified:             0
% 1.59/1.08  inst_num_child_elim:                    0
% 1.59/1.08  inst_num_of_dismatching_blockings:      146
% 1.59/1.08  inst_num_of_non_proper_insts:           250
% 1.59/1.08  inst_num_of_duplicates:                 0
% 1.59/1.08  inst_inst_num_from_inst_to_res:         0
% 1.59/1.08  inst_dismatching_checking_time:         0.
% 1.59/1.08  
% 1.59/1.08  ------ Resolution
% 1.59/1.08  
% 1.59/1.08  res_num_of_clauses:                     0
% 1.59/1.08  res_num_in_passive:                     0
% 1.59/1.08  res_num_in_active:                      0
% 1.59/1.08  res_num_of_loops:                       72
% 1.59/1.08  res_forward_subset_subsumed:            23
% 1.59/1.08  res_backward_subset_subsumed:           0
% 1.59/1.08  res_forward_subsumed:                   0
% 1.59/1.08  res_backward_subsumed:                  0
% 1.59/1.08  res_forward_subsumption_resolution:     0
% 1.59/1.08  res_backward_subsumption_resolution:    0
% 1.59/1.08  res_clause_to_clause_subsumption:       98
% 1.59/1.08  res_orphan_elimination:                 0
% 1.59/1.08  res_tautology_del:                      23
% 1.59/1.08  res_num_eq_res_simplified:              0
% 1.59/1.08  res_num_sel_changes:                    0
% 1.59/1.08  res_moves_from_active_to_pass:          0
% 1.59/1.08  
% 1.59/1.08  ------ Superposition
% 1.59/1.08  
% 1.59/1.08  sup_time_total:                         0.
% 1.59/1.08  sup_time_generating:                    0.
% 1.59/1.08  sup_time_sim_full:                      0.
% 1.59/1.08  sup_time_sim_immed:                     0.
% 1.59/1.08  
% 1.59/1.08  sup_num_of_clauses:                     32
% 1.59/1.08  sup_num_in_active:                      25
% 1.59/1.08  sup_num_in_passive:                     7
% 1.59/1.08  sup_num_of_loops:                       28
% 1.59/1.08  sup_fw_superposition:                   20
% 1.59/1.08  sup_bw_superposition:                   4
% 1.59/1.08  sup_immediate_simplified:               3
% 1.59/1.08  sup_given_eliminated:                   0
% 1.59/1.08  comparisons_done:                       0
% 1.59/1.08  comparisons_avoided:                    0
% 1.59/1.08  
% 1.59/1.08  ------ Simplifications
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  sim_fw_subset_subsumed:                 0
% 1.59/1.08  sim_bw_subset_subsumed:                 0
% 1.59/1.08  sim_fw_subsumed:                        1
% 1.59/1.08  sim_bw_subsumed:                        0
% 1.59/1.08  sim_fw_subsumption_res:                 0
% 1.59/1.08  sim_bw_subsumption_res:                 0
% 1.59/1.08  sim_tautology_del:                      0
% 1.59/1.08  sim_eq_tautology_del:                   0
% 1.59/1.08  sim_eq_res_simp:                        1
% 1.59/1.08  sim_fw_demodulated:                     1
% 1.59/1.08  sim_bw_demodulated:                     3
% 1.59/1.08  sim_light_normalised:                   7
% 1.59/1.08  sim_joinable_taut:                      0
% 1.59/1.08  sim_joinable_simp:                      0
% 1.59/1.08  sim_ac_normalised:                      0
% 1.59/1.08  sim_smt_subsumption:                    0
% 1.59/1.08  
%------------------------------------------------------------------------------
