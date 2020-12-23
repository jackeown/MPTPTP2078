%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:26 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 516 expanded)
%              Number of clauses        :   66 ( 140 expanded)
%              Number of leaves         :   17 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  314 (2324 expanded)
%              Number of equality atoms :  148 ( 748 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f59,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f45,f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_633,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_632,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_636,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1980,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_636])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2538,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_20])).

cnf(c_2539,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2538])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_644,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2544,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_644])).

cnf(c_2788,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_633,c_2544])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3100,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2788,c_1])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_641,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3604,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_632,c_641])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_635,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1056,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_635])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1343,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1056,c_17,c_16,c_894])).

cnf(c_3813,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3604,c_1343])).

cnf(c_5245,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3100,c_3813])).

cnf(c_5246,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5245,c_3604])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_643,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_645,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1334,plain,
    ( k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_643,c_645])).

cnf(c_1464,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1334])).

cnf(c_5258,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_5246,c_1464])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_642,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6719,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_642])).

cnf(c_7309,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_6719])).

cnf(c_7469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7309,c_20])).

cnf(c_7470,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7469])).

cnf(c_7478,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_632,c_7470])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_637,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3598,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_637])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3825,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3598,c_17,c_16,c_891])).

cnf(c_7480,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7478,c_3825])).

cnf(c_7798,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_5258,c_7480])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_639,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5746,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_639])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_832,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_833,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_6707,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5746,c_19,c_20,c_21,c_833])).

cnf(c_7800,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7798,c_6707])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_634,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3792,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3604,c_634])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7800,c_5246,c_3792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:57:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.73/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.99  
% 3.73/0.99  ------  iProver source info
% 3.73/0.99  
% 3.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.99  git: non_committed_changes: false
% 3.73/0.99  git: last_make_outside_of_git: false
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  ------ Parsing...
% 3.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  ------ Proving...
% 3.73/0.99  ------ Problem Properties 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  clauses                                 19
% 3.73/0.99  conjectures                             5
% 3.73/0.99  EPR                                     2
% 3.73/0.99  Horn                                    18
% 3.73/0.99  unary                                   7
% 3.73/0.99  binary                                  5
% 3.73/0.99  lits                                    40
% 3.73/0.99  lits eq                                 11
% 3.73/0.99  fd_pure                                 0
% 3.73/0.99  fd_pseudo                               0
% 3.73/0.99  fd_cond                                 0
% 3.73/0.99  fd_pseudo_cond                          0
% 3.73/0.99  AC symbols                              0
% 3.73/0.99  
% 3.73/0.99  ------ Input Options Time Limit: Unbounded
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  Current options:
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS status Theorem for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  fof(f17,conjecture,(
% 3.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f18,negated_conjecture,(
% 3.73/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.73/0.99    inference(negated_conjecture,[],[f17])).
% 3.73/0.99  
% 3.73/0.99  fof(f33,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f18])).
% 3.73/0.99  
% 3.73/0.99  fof(f34,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/0.99    inference(flattening,[],[f33])).
% 3.73/0.99  
% 3.73/0.99  fof(f35,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/0.99    inference(nnf_transformation,[],[f34])).
% 3.73/0.99  
% 3.73/0.99  fof(f36,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/0.99    inference(flattening,[],[f35])).
% 3.73/0.99  
% 3.73/0.99  fof(f38,plain,(
% 3.73/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f37,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f39,plain,(
% 3.73/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 3.73/0.99  
% 3.73/0.99  fof(f59,plain,(
% 3.73/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  fof(f58,plain,(
% 3.73/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  fof(f15,axiom,(
% 3.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f30,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f15])).
% 3.73/0.99  
% 3.73/0.99  fof(f31,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/0.99    inference(flattening,[],[f30])).
% 3.73/0.99  
% 3.73/0.99  fof(f54,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f31])).
% 3.73/0.99  
% 3.73/0.99  fof(f57,plain,(
% 3.73/0.99    l1_pre_topc(sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  fof(f4,axiom,(
% 3.73/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f20,plain,(
% 3.73/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f4])).
% 3.73/0.99  
% 3.73/0.99  fof(f43,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f20])).
% 3.73/0.99  
% 3.73/0.99  fof(f6,axiom,(
% 3.73/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f45,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f6])).
% 3.73/0.99  
% 3.73/0.99  fof(f64,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.73/0.99    inference(definition_unfolding,[],[f43,f45])).
% 3.73/0.99  
% 3.73/0.99  fof(f1,axiom,(
% 3.73/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f40,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f1])).
% 3.73/0.99  
% 3.73/0.99  fof(f62,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.73/0.99    inference(definition_unfolding,[],[f40,f45,f45])).
% 3.73/0.99  
% 3.73/0.99  fof(f10,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f23,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f10])).
% 3.73/0.99  
% 3.73/0.99  fof(f49,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f23])).
% 3.73/0.99  
% 3.73/0.99  fof(f16,axiom,(
% 3.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f32,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f16])).
% 3.73/0.99  
% 3.73/0.99  fof(f55,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f32])).
% 3.73/0.99  
% 3.73/0.99  fof(f7,axiom,(
% 3.73/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f46,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f7])).
% 3.73/0.99  
% 3.73/0.99  fof(f5,axiom,(
% 3.73/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f44,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f5])).
% 3.73/0.99  
% 3.73/0.99  fof(f3,axiom,(
% 3.73/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f19,plain,(
% 3.73/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f3])).
% 3.73/0.99  
% 3.73/0.99  fof(f42,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f19])).
% 3.73/0.99  
% 3.73/0.99  fof(f8,axiom,(
% 3.73/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f47,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f8])).
% 3.73/0.99  
% 3.73/0.99  fof(f63,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.73/0.99    inference(definition_unfolding,[],[f42,f47])).
% 3.73/0.99  
% 3.73/0.99  fof(f11,axiom,(
% 3.73/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f24,plain,(
% 3.73/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f11])).
% 3.73/0.99  
% 3.73/0.99  fof(f25,plain,(
% 3.73/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.73/0.99    inference(flattening,[],[f24])).
% 3.73/0.99  
% 3.73/0.99  fof(f50,plain,(
% 3.73/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f9,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f21,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.73/0.99    inference(ennf_transformation,[],[f9])).
% 3.73/0.99  
% 3.73/0.99  fof(f22,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.99    inference(flattening,[],[f21])).
% 3.73/0.99  
% 3.73/0.99  fof(f48,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f22])).
% 3.73/0.99  
% 3.73/0.99  fof(f65,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.99    inference(definition_unfolding,[],[f48,f47])).
% 3.73/0.99  
% 3.73/0.99  fof(f14,axiom,(
% 3.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f29,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f14])).
% 3.73/0.99  
% 3.73/0.99  fof(f53,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f29])).
% 3.73/0.99  
% 3.73/0.99  fof(f12,axiom,(
% 3.73/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f26,plain,(
% 3.73/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f12])).
% 3.73/0.99  
% 3.73/0.99  fof(f27,plain,(
% 3.73/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/0.99    inference(flattening,[],[f26])).
% 3.73/0.99  
% 3.73/0.99  fof(f51,plain,(
% 3.73/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f27])).
% 3.73/0.99  
% 3.73/0.99  fof(f56,plain,(
% 3.73/0.99    v2_pre_topc(sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  fof(f60,plain,(
% 3.73/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  cnf(c_15,negated_conjecture,
% 3.73/0.99      ( v4_pre_topc(sK1,sK0)
% 3.73/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_633,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.73/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16,negated_conjecture,
% 3.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_632,plain,
% 3.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12,plain,
% 3.73/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.99      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.73/0.99      | ~ l1_pre_topc(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_636,plain,
% 3.73/0.99      ( v4_pre_topc(X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/0.99      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.73/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1980,plain,
% 3.73/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_636]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_17,negated_conjecture,
% 3.73/0.99      ( l1_pre_topc(sK0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_20,plain,
% 3.73/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2538,plain,
% 3.73/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.73/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_1980,c_20]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2539,plain,
% 3.73/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_2538]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3,plain,
% 3.73/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.73/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_644,plain,
% 3.73/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.73/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2544,plain,
% 3.73/0.99      ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 3.73/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2539,c_644]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2788,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.73/0.99      | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_633,c_2544]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1,plain,
% 3.73/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3100,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.73/0.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2788,c_1]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.73/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_641,plain,
% 3.73/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3604,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_641]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_13,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.99      | ~ l1_pre_topc(X1)
% 3.73/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_635,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1056,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_635]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_894,plain,
% 3.73/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/0.99      | ~ l1_pre_topc(sK0)
% 3.73/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1343,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_1056,c_17,c_16,c_894]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3813,plain,
% 3.73/0.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_3604,c_1343]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5245,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.73/0.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(light_normalisation,[status(thm)],[c_3100,c_3813]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5246,plain,
% 3.73/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_5245,c_3604]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5,plain,
% 3.73/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4,plain,
% 3.73/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_643,plain,
% 3.73/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2,plain,
% 3.73/0.99      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 3.73/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_645,plain,
% 3.73/0.99      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 3.73/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1334,plain,
% 3.73/0.99      ( k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) = X0 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_643,c_645]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1464,plain,
% 3.73/0.99      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_5,c_1334]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5258,plain,
% 3.73/0.99      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_5246,c_1464]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_8,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.99      | ~ l1_pre_topc(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_640,plain,
% 3.73/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.73/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_6,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.73/0.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_642,plain,
% 3.73/0.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_6719,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_642]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7309,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_640,c_6719]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7469,plain,
% 3.73/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_7309,c_20]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7470,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_7469]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7478,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_7470]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.99      | ~ l1_pre_topc(X1)
% 3.73/0.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_637,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3598,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_637]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_891,plain,
% 3.73/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/0.99      | ~ l1_pre_topc(sK0)
% 3.73/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3825,plain,
% 3.73/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_3598,c_17,c_16,c_891]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7480,plain,
% 3.73/0.99      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.73/0.99      inference(light_normalisation,[status(thm)],[c_7478,c_3825]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7798,plain,
% 3.73/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_5258,c_7480]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.73/0.99      | ~ v2_pre_topc(X0)
% 3.73/0.99      | ~ l1_pre_topc(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_639,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/0.99      | v2_pre_topc(X0) != iProver_top
% 3.73/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5746,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.73/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_632,c_639]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_18,negated_conjecture,
% 3.73/0.99      ( v2_pre_topc(sK0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_19,plain,
% 3.73/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_21,plain,
% 3.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_832,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.73/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/0.99      | ~ v2_pre_topc(sK0)
% 3.73/0.99      | ~ l1_pre_topc(sK0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_833,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.73/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.73/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_6707,plain,
% 3.73/0.99      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_5746,c_19,c_20,c_21,c_833]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7800,plain,
% 3.73/0.99      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_7798,c_6707]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_14,negated_conjecture,
% 3.73/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 3.73/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_634,plain,
% 3.73/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.73/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3792,plain,
% 3.73/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.73/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_3604,c_634]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(contradiction,plain,
% 3.73/0.99      ( $false ),
% 3.73/0.99      inference(minisat,[status(thm)],[c_7800,c_5246,c_3792]) ).
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  ------                               Statistics
% 3.73/0.99  
% 3.73/0.99  ------ Selected
% 3.73/0.99  
% 3.73/0.99  total_time:                             0.276
% 3.73/0.99  
%------------------------------------------------------------------------------
