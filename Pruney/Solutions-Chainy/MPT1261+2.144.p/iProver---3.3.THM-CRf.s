%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:45 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 567 expanded)
%              Number of clauses        :   68 ( 154 expanded)
%              Number of leaves         :   16 ( 131 expanded)
%              Depth                    :   19
%              Number of atoms          :  305 (2374 expanded)
%              Number of equality atoms :  146 ( 800 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f41,f41])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_589,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_592,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1008,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_592])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1282,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1008,c_16,c_15,c_848])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_597,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2042,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_589,c_597])).

cnf(c_2057,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1282,c_2042])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2499,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2057,c_7])).

cnf(c_14,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_590,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2045,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2042,c_590])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_593,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1753,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_593])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2333,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1753,c_19])).

cnf(c_2334,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2333])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_600,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1,c_7])).

cnf(c_622,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_600,c_616])).

cnf(c_2339,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_622])).

cnf(c_2727,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2045,c_2339])).

cnf(c_3047,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2499,c_2727])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_599,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1431,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_599,c_622])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_612,plain,
    ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_7,c_2])).

cnf(c_1558,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1431,c_612])).

cnf(c_4209,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3047,c_1558])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_596,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_598,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3324,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_598])).

cnf(c_3510,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_3324])).

cnf(c_3935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_19])).

cnf(c_3936,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3935])).

cnf(c_3944,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_589,c_3936])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_594,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2925,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_594])).

cnf(c_845,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3504,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2925,c_16,c_15,c_845])).

cnf(c_3946,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3944,c_3504])).

cnf(c_6252,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4209,c_3946])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_595,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3349,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_595])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_784,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_785,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_3724,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3349,c_18,c_19,c_20,c_785])).

cnf(c_6395,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6252,c_3724])).

cnf(c_13,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_591,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2046,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2042,c_591])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6395,c_3047,c_2046])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 18
% 3.61/0.99  conjectures                             5
% 3.61/0.99  EPR                                     2
% 3.61/0.99  Horn                                    17
% 3.61/0.99  unary                                   8
% 3.61/0.99  binary                                  4
% 3.61/0.99  lits                                    36
% 3.61/0.99  lits eq                                 11
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 0
% 3.61/0.99  fd_pseudo_cond                          0
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Input Options Time Limit: Unbounded
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f15,conjecture,(
% 3.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f16,negated_conjecture,(
% 3.61/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.61/0.99    inference(negated_conjecture,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f29,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f16])).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.99    inference(flattening,[],[f29])).
% 3.61/0.99  
% 3.61/0.99  fof(f31,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.99    inference(nnf_transformation,[],[f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f32,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.99    inference(flattening,[],[f31])).
% 3.61/0.99  
% 3.61/0.99  fof(f34,plain,(
% 3.61/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f33,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.61/0.99  
% 3.61/0.99  fof(f52,plain,(
% 3.61/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f14,axiom,(
% 3.61/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f28,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f14])).
% 3.61/0.99  
% 3.61/0.99  fof(f49,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f28])).
% 3.61/0.99  
% 3.61/0.99  fof(f51,plain,(
% 3.61/0.99    l1_pre_topc(sK0)),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f8,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f20,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f8])).
% 3.61/0.99  
% 3.61/0.99  fof(f43,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f20])).
% 3.61/0.99  
% 3.61/0.99  fof(f9,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f44,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f9])).
% 3.61/0.99  
% 3.61/0.99  fof(f6,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f41,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f6])).
% 3.61/0.99  
% 3.61/0.99  fof(f59,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.61/0.99    inference(definition_unfolding,[],[f44,f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f53,plain,(
% 3.61/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f13,axiom,(
% 3.61/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f26,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f13])).
% 3.61/0.99  
% 3.61/0.99  fof(f27,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.99    inference(flattening,[],[f26])).
% 3.61/0.99  
% 3.61/0.99  fof(f48,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f27])).
% 3.61/0.99  
% 3.61/0.99  fof(f4,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f17,plain,(
% 3.61/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f4])).
% 3.61/0.99  
% 3.61/0.99  fof(f39,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f17])).
% 3.61/0.99  
% 3.61/0.99  fof(f58,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(definition_unfolding,[],[f39,f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f56,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.61/0.99    inference(definition_unfolding,[],[f36,f41,f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f5,axiom,(
% 3.61/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f40,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f5])).
% 3.61/0.99  
% 3.61/0.99  fof(f3,axiom,(
% 3.61/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f3])).
% 3.61/0.99  
% 3.61/0.99  fof(f57,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.61/0.99    inference(definition_unfolding,[],[f38,f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f10,axiom,(
% 3.61/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.61/0.99    inference(flattening,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  fof(f45,plain,(
% 3.61/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f7,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f18,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.61/0.99    inference(ennf_transformation,[],[f7])).
% 3.61/0.99  
% 3.61/0.99  fof(f19,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.99    inference(flattening,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f42,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f19])).
% 3.61/0.99  
% 3.61/0.99  fof(f12,axiom,(
% 3.61/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f25,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f12])).
% 3.61/0.99  
% 3.61/0.99  fof(f47,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f25])).
% 3.61/0.99  
% 3.61/0.99  fof(f11,axiom,(
% 3.61/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.61/0.99    inference(flattening,[],[f23])).
% 3.61/0.99  
% 3.61/0.99  fof(f46,plain,(
% 3.61/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f24])).
% 3.61/0.99  
% 3.61/0.99  fof(f50,plain,(
% 3.61/0.99    v2_pre_topc(sK0)),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f54,plain,(
% 3.61/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,negated_conjecture,
% 3.61/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_589,plain,
% 3.61/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.99      | ~ l1_pre_topc(X1)
% 3.61/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_592,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.61/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1008,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_592]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_16,negated_conjecture,
% 3.61/0.99      ( l1_pre_topc(sK0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_848,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.61/0.99      | ~ l1_pre_topc(sK0)
% 3.61/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1282,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1008,c_16,c_15,c_848]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_597,plain,
% 3.61/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.61/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2042,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_597]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2057,plain,
% 3.61/0.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1282,c_2042]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2499,plain,
% 3.61/0.99      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2057,c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,negated_conjecture,
% 3.61/0.99      ( v4_pre_topc(sK1,sK0)
% 3.61/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_590,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2045,plain,
% 3.61/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_2042,c_590]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,plain,
% 3.61/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.99      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.61/0.99      | ~ l1_pre_topc(X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_593,plain,
% 3.61/0.99      ( v4_pre_topc(X0,X1) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.61/0.99      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.61/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1753,plain,
% 3.61/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.61/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_593]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_19,plain,
% 3.61/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2333,plain,
% 3.61/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.61/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1753,c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2334,plain,
% 3.61/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.61/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_2333]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_600,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_616,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1,c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_622,plain,
% 3.61/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X1
% 3.61/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_600,c_616]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2339,plain,
% 3.61/0.99      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 3.61/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2334,c_622]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2727,plain,
% 3.61/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.99      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2045,c_2339]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3047,plain,
% 3.61/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2499,c_2727]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4,plain,
% 3.61/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_599,plain,
% 3.61/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1431,plain,
% 3.61/0.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_599,c_622]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_612,plain,
% 3.61/0.99      ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_7,c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1558,plain,
% 3.61/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1431,c_612]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4209,plain,
% 3.61/0.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3047,c_1558]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.99      | ~ l1_pre_topc(X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_596,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.61/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_598,plain,
% 3.61/0.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.61/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3324,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_598]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3510,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_596,c_3324]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3935,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.61/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3510,c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3936,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 3.61/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_3935]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3944,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_3936]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.99      | ~ l1_pre_topc(X1)
% 3.61/0.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_594,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.61/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2925,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_594]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_845,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.61/0.99      | ~ l1_pre_topc(sK0)
% 3.61/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3504,plain,
% 3.61/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_2925,c_16,c_15,c_845]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3946,plain,
% 3.61/0.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_3944,c_3504]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6252,plain,
% 3.61/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4209,c_3946]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.61/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.61/0.99      | ~ v2_pre_topc(X0)
% 3.61/0.99      | ~ l1_pre_topc(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_595,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.61/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.99      | v2_pre_topc(X0) != iProver_top
% 3.61/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3349,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.61/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_589,c_595]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17,negated_conjecture,
% 3.61/0.99      ( v2_pre_topc(sK0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18,plain,
% 3.61/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_20,plain,
% 3.61/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_784,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.61/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.61/0.99      | ~ v2_pre_topc(sK0)
% 3.61/0.99      | ~ l1_pre_topc(sK0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_785,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.61/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.61/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.61/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3724,plain,
% 3.61/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3349,c_18,c_19,c_20,c_785]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6395,plain,
% 3.61/0.99      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_6252,c_3724]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,negated_conjecture,
% 3.61/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 3.61/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_591,plain,
% 3.61/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.61/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2046,plain,
% 3.61/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.61/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_2042,c_591]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,[status(thm)],[c_6395,c_3047,c_2046]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ Selected
% 3.61/0.99  
% 3.61/0.99  total_time:                             0.235
% 3.61/0.99  
%------------------------------------------------------------------------------
