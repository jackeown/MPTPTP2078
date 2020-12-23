%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:28 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 442 expanded)
%              Number of clauses        :   50 ( 120 expanded)
%              Number of leaves         :   13 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  271 (2077 expanded)
%              Number of equality atoms :  123 ( 670 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_875,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_883,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1748,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_875,c_883])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_876,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1866,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1748,c_876])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_881,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7082,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_881])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7398,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7082,c_23])).

cnf(c_7399,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7398])).

cnf(c_7404,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1866,c_7399])).

cnf(c_9,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_887,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_889,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1526,plain,
    ( k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_887,c_889])).

cnf(c_1616,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1526])).

cnf(c_7931,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_7404,c_1616])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_878,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7060,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_878])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_884,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5806,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_884])).

cnf(c_5828,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_880,c_5806])).

cnf(c_6320,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5828,c_23])).

cnf(c_6321,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6320])).

cnf(c_6329,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_875,c_6321])).

cnf(c_7063,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7060,c_6329])).

cnf(c_7699,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7063,c_23])).

cnf(c_7945,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_7931,c_7699])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_879,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7217,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_875,c_879])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7406,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7217,c_20,c_19,c_1128])).

cnf(c_7950,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7945,c_7406])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1097,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7950,c_7945,c_1097,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.61/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.96  
% 3.61/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.96  
% 3.61/0.96  ------  iProver source info
% 3.61/0.96  
% 3.61/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.96  git: non_committed_changes: false
% 3.61/0.96  git: last_make_outside_of_git: false
% 3.61/0.96  
% 3.61/0.96  ------ 
% 3.61/0.96  ------ Parsing...
% 3.61/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.96  
% 3.61/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.61/0.96  
% 3.61/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.96  
% 3.61/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.96  ------ Proving...
% 3.61/0.96  ------ Problem Properties 
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  clauses                                 21
% 3.61/0.96  conjectures                             5
% 3.61/0.96  EPR                                     5
% 3.61/0.96  Horn                                    20
% 3.61/0.96  unary                                   8
% 3.61/0.96  binary                                  6
% 3.61/0.96  lits                                    44
% 3.61/0.96  lits eq                                 12
% 3.61/0.96  fd_pure                                 0
% 3.61/0.96  fd_pseudo                               0
% 3.61/0.96  fd_cond                                 0
% 3.61/0.96  fd_pseudo_cond                          1
% 3.61/0.96  AC symbols                              0
% 3.61/0.96  
% 3.61/0.96  ------ Input Options Time Limit: Unbounded
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  ------ 
% 3.61/0.96  Current options:
% 3.61/0.96  ------ 
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  ------ Proving...
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  % SZS status Theorem for theBenchmark.p
% 3.61/0.96  
% 3.61/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.96  
% 3.61/0.96  fof(f16,conjecture,(
% 3.61/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f17,negated_conjecture,(
% 3.61/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.61/0.96    inference(negated_conjecture,[],[f16])).
% 3.61/0.96  
% 3.61/0.96  fof(f30,plain,(
% 3.61/0.96    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.61/0.96    inference(ennf_transformation,[],[f17])).
% 3.61/0.96  
% 3.61/0.96  fof(f31,plain,(
% 3.61/0.96    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.96    inference(flattening,[],[f30])).
% 3.61/0.96  
% 3.61/0.96  fof(f34,plain,(
% 3.61/0.96    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.96    inference(nnf_transformation,[],[f31])).
% 3.61/0.96  
% 3.61/0.96  fof(f35,plain,(
% 3.61/0.96    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.96    inference(flattening,[],[f34])).
% 3.61/0.96  
% 3.61/0.96  fof(f37,plain,(
% 3.61/0.96    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.61/0.96    introduced(choice_axiom,[])).
% 3.61/0.96  
% 3.61/0.96  fof(f36,plain,(
% 3.61/0.96    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.61/0.96    introduced(choice_axiom,[])).
% 3.61/0.96  
% 3.61/0.96  fof(f38,plain,(
% 3.61/0.96    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.61/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 3.61/0.96  
% 3.61/0.96  fof(f59,plain,(
% 3.61/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.61/0.96    inference(cnf_transformation,[],[f38])).
% 3.61/0.96  
% 3.61/0.96  fof(f11,axiom,(
% 3.61/0.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f23,plain,(
% 3.61/0.96    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.96    inference(ennf_transformation,[],[f11])).
% 3.61/0.96  
% 3.61/0.96  fof(f51,plain,(
% 3.61/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.96    inference(cnf_transformation,[],[f23])).
% 3.61/0.96  
% 3.61/0.96  fof(f60,plain,(
% 3.61/0.96    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.61/0.96    inference(cnf_transformation,[],[f38])).
% 3.61/0.96  
% 3.61/0.96  fof(f12,axiom,(
% 3.61/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f24,plain,(
% 3.61/0.96    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.96    inference(ennf_transformation,[],[f12])).
% 3.61/0.96  
% 3.61/0.96  fof(f25,plain,(
% 3.61/0.96    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.96    inference(flattening,[],[f24])).
% 3.61/0.96  
% 3.61/0.96  fof(f52,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f25])).
% 3.61/0.96  
% 3.61/0.96  fof(f58,plain,(
% 3.61/0.96    l1_pre_topc(sK0)),
% 3.61/0.96    inference(cnf_transformation,[],[f38])).
% 3.61/0.96  
% 3.61/0.96  fof(f8,axiom,(
% 3.61/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f48,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f8])).
% 3.61/0.96  
% 3.61/0.96  fof(f5,axiom,(
% 3.61/0.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f45,plain,(
% 3.61/0.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f5])).
% 3.61/0.96  
% 3.61/0.96  fof(f2,axiom,(
% 3.61/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f18,plain,(
% 3.61/0.96    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.61/0.96    inference(ennf_transformation,[],[f2])).
% 3.61/0.96  
% 3.61/0.96  fof(f42,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f18])).
% 3.61/0.96  
% 3.61/0.96  fof(f9,axiom,(
% 3.61/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f49,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.61/0.96    inference(cnf_transformation,[],[f9])).
% 3.61/0.96  
% 3.61/0.96  fof(f62,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.61/0.96    inference(definition_unfolding,[],[f42,f49])).
% 3.61/0.96  
% 3.61/0.96  fof(f15,axiom,(
% 3.61/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f29,plain,(
% 3.61/0.96    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.96    inference(ennf_transformation,[],[f15])).
% 3.61/0.96  
% 3.61/0.96  fof(f56,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f29])).
% 3.61/0.96  
% 3.61/0.96  fof(f13,axiom,(
% 3.61/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f26,plain,(
% 3.61/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.61/0.96    inference(ennf_transformation,[],[f13])).
% 3.61/0.96  
% 3.61/0.96  fof(f27,plain,(
% 3.61/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.61/0.96    inference(flattening,[],[f26])).
% 3.61/0.96  
% 3.61/0.96  fof(f54,plain,(
% 3.61/0.96    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f27])).
% 3.61/0.96  
% 3.61/0.96  fof(f10,axiom,(
% 3.61/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f21,plain,(
% 3.61/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.61/0.96    inference(ennf_transformation,[],[f10])).
% 3.61/0.96  
% 3.61/0.96  fof(f22,plain,(
% 3.61/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.96    inference(flattening,[],[f21])).
% 3.61/0.96  
% 3.61/0.96  fof(f50,plain,(
% 3.61/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.96    inference(cnf_transformation,[],[f22])).
% 3.61/0.96  
% 3.61/0.96  fof(f66,plain,(
% 3.61/0.96    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.96    inference(definition_unfolding,[],[f50,f49])).
% 3.61/0.96  
% 3.61/0.96  fof(f14,axiom,(
% 3.61/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.61/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.96  
% 3.61/0.96  fof(f28,plain,(
% 3.61/0.96    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.96    inference(ennf_transformation,[],[f14])).
% 3.61/0.96  
% 3.61/0.96  fof(f55,plain,(
% 3.61/0.96    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f28])).
% 3.61/0.96  
% 3.61/0.96  fof(f53,plain,(
% 3.61/0.96    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.96    inference(cnf_transformation,[],[f25])).
% 3.61/0.96  
% 3.61/0.96  fof(f61,plain,(
% 3.61/0.96    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.61/0.96    inference(cnf_transformation,[],[f38])).
% 3.61/0.96  
% 3.61/0.96  fof(f57,plain,(
% 3.61/0.96    v2_pre_topc(sK0)),
% 3.61/0.96    inference(cnf_transformation,[],[f38])).
% 3.61/0.96  
% 3.61/0.96  cnf(c_19,negated_conjecture,
% 3.61/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.61/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_875,plain,
% 3.61/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_11,plain,
% 3.61/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.96      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.61/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_883,plain,
% 3.61/0.96      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.61/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1748,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_883]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_18,negated_conjecture,
% 3.61/0.96      ( v4_pre_topc(sK1,sK0)
% 3.61/0.96      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_876,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.96      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1866,plain,
% 3.61/0.96      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.96      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.61/0.96      inference(demodulation,[status(thm)],[c_1748,c_876]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_13,plain,
% 3.61/0.96      ( ~ v4_pre_topc(X0,X1)
% 3.61/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | ~ l1_pre_topc(X1)
% 3.61/0.96      | k2_pre_topc(X1,X0) = X0 ),
% 3.61/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_881,plain,
% 3.61/0.96      ( k2_pre_topc(X0,X1) = X1
% 3.61/0.96      | v4_pre_topc(X1,X0) != iProver_top
% 3.61/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7082,plain,
% 3.61/0.96      ( k2_pre_topc(sK0,sK1) = sK1
% 3.61/0.96      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.61/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_881]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_20,negated_conjecture,
% 3.61/0.96      ( l1_pre_topc(sK0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_23,plain,
% 3.61/0.96      ( l1_pre_topc(sK0) = iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7398,plain,
% 3.61/0.96      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.61/0.96      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.61/0.96      inference(global_propositional_subsumption,
% 3.61/0.96                [status(thm)],
% 3.61/0.96                [c_7082,c_23]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7399,plain,
% 3.61/0.96      ( k2_pre_topc(sK0,sK1) = sK1
% 3.61/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.61/0.96      inference(renaming,[status(thm)],[c_7398]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7404,plain,
% 3.61/0.96      ( k2_pre_topc(sK0,sK1) = sK1
% 3.61/0.96      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_1866,c_7399]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_9,plain,
% 3.61/0.96      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_6,plain,
% 3.61/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_887,plain,
% 3.61/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_3,plain,
% 3.61/0.96      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 3.61/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_889,plain,
% 3.61/0.96      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 3.61/0.96      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1526,plain,
% 3.61/0.96      ( k3_tarski(k2_tarski(k4_xboole_0(X0,X1),X0)) = X0 ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_887,c_889]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1616,plain,
% 3.61/0.96      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_9,c_1526]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7931,plain,
% 3.61/0.96      ( k2_pre_topc(sK0,sK1) = sK1
% 3.61/0.96      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_7404,c_1616]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_16,plain,
% 3.61/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | ~ l1_pre_topc(X1)
% 3.61/0.96      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_878,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.61/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7060,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.61/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_878]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_14,plain,
% 3.61/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | ~ l1_pre_topc(X1) ),
% 3.61/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_880,plain,
% 3.61/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.61/0.96      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.61/0.96      | l1_pre_topc(X1) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_10,plain,
% 3.61/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/0.96      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.61/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_884,plain,
% 3.61/0.96      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.61/0.96      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.61/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_5806,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 3.61/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_884]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_5828,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.61/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.61/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_880,c_5806]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_6320,plain,
% 3.61/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.61/0.96      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.61/0.96      inference(global_propositional_subsumption,
% 3.61/0.96                [status(thm)],
% 3.61/0.96                [c_5828,c_23]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_6321,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.61/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.61/0.96      inference(renaming,[status(thm)],[c_6320]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_6329,plain,
% 3.61/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_6321]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7063,plain,
% 3.61/0.96      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 3.61/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.96      inference(demodulation,[status(thm)],[c_7060,c_6329]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7699,plain,
% 3.61/0.96      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.61/0.96      inference(global_propositional_subsumption,
% 3.61/0.96                [status(thm)],
% 3.61/0.96                [c_7063,c_23]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7945,plain,
% 3.61/0.96      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.61/0.96      inference(demodulation,[status(thm)],[c_7931,c_7699]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_15,plain,
% 3.61/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | ~ l1_pre_topc(X1)
% 3.61/0.96      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_879,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.61/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.61/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.61/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7217,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.61/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.61/0.96      inference(superposition,[status(thm)],[c_875,c_879]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1128,plain,
% 3.61/0.96      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.61/0.96      | ~ l1_pre_topc(sK0)
% 3.61/0.96      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7406,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(global_propositional_subsumption,
% 3.61/0.96                [status(thm)],
% 3.61/0.96                [c_7217,c_20,c_19,c_1128]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_7950,plain,
% 3.61/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(demodulation,[status(thm)],[c_7945,c_7406]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_12,plain,
% 3.61/0.96      ( v4_pre_topc(X0,X1)
% 3.61/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.61/0.96      | ~ l1_pre_topc(X1)
% 3.61/0.96      | ~ v2_pre_topc(X1)
% 3.61/0.96      | k2_pre_topc(X1,X0) != X0 ),
% 3.61/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_1097,plain,
% 3.61/0.96      ( v4_pre_topc(sK1,sK0)
% 3.61/0.96      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.61/0.96      | ~ l1_pre_topc(sK0)
% 3.61/0.96      | ~ v2_pre_topc(sK0)
% 3.61/0.96      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.61/0.96      inference(instantiation,[status(thm)],[c_12]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_17,negated_conjecture,
% 3.61/0.96      ( ~ v4_pre_topc(sK1,sK0)
% 3.61/0.96      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.61/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(c_21,negated_conjecture,
% 3.61/0.96      ( v2_pre_topc(sK0) ),
% 3.61/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.96  
% 3.61/0.96  cnf(contradiction,plain,
% 3.61/0.96      ( $false ),
% 3.61/0.96      inference(minisat,
% 3.61/0.96                [status(thm)],
% 3.61/0.96                [c_7950,c_7945,c_1097,c_17,c_19,c_20,c_21]) ).
% 3.61/0.96  
% 3.61/0.96  
% 3.61/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.96  
% 3.61/0.96  ------                               Statistics
% 3.61/0.96  
% 3.61/0.96  ------ Selected
% 3.61/0.96  
% 3.61/0.96  total_time:                             0.216
% 3.61/0.96  
%------------------------------------------------------------------------------
