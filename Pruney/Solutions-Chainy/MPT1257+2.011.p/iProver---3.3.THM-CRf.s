%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:14 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 325 expanded)
%              Number of clauses        :   64 ( 112 expanded)
%              Number of leaves         :   16 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  265 ( 859 expanded)
%              Number of equality atoms :  110 ( 163 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_xboole_0(k1_tops_1(X0,sK1),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f42,f41])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_567,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_570,plain,
    ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3057,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_570])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4300,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3057,c_20,c_19,c_807])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4303,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4300,c_571])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_799,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_800,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_5651,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_21,c_22,c_800])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_577,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6319,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_577])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_580,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1279,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_567,c_580])).

cnf(c_6343,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6319,c_1279])).

cnf(c_6988,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_5651,c_6343])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_584,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_569,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1592,plain,
    ( k4_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_569])).

cnf(c_8274,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_1592])).

cnf(c_8297,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8274,c_4300])).

cnf(c_9338,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8297,c_21])).

cnf(c_11789,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_6988,c_9338])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_583,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2495,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_583])).

cnf(c_2775,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_581,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2784,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2775,c_581])).

cnf(c_11803,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_11789,c_2784])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_573,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3773,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_573])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4306,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_20,c_19,c_836])).

cnf(c_11805,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11803,c_4306])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_582,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_820,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_567,c_582])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_576])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3846,c_579])).

cnf(c_9055,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2775,c_6711])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_586,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11404,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9055,c_586])).

cnf(c_12482,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11805,c_11404])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12482,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:51:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 4.02/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/0.94  
% 4.02/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.94  
% 4.02/0.94  ------  iProver source info
% 4.02/0.94  
% 4.02/0.94  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.94  git: non_committed_changes: false
% 4.02/0.94  git: last_make_outside_of_git: false
% 4.02/0.94  
% 4.02/0.94  ------ 
% 4.02/0.94  ------ Parsing...
% 4.02/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.94  
% 4.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.02/0.94  
% 4.02/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.94  
% 4.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.94  ------ Proving...
% 4.02/0.94  ------ Problem Properties 
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  clauses                                 21
% 4.02/0.94  conjectures                             3
% 4.02/0.94  EPR                                     1
% 4.02/0.94  Horn                                    21
% 4.02/0.94  unary                                   3
% 4.02/0.94  binary                                  7
% 4.02/0.94  lits                                    54
% 4.02/0.94  lits eq                                 7
% 4.02/0.94  fd_pure                                 0
% 4.02/0.94  fd_pseudo                               0
% 4.02/0.94  fd_cond                                 0
% 4.02/0.94  fd_pseudo_cond                          0
% 4.02/0.94  AC symbols                              0
% 4.02/0.94  
% 4.02/0.94  ------ Input Options Time Limit: Unbounded
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  ------ 
% 4.02/0.94  Current options:
% 4.02/0.94  ------ 
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  ------ Proving...
% 4.02/0.94  
% 4.02/0.94  
% 4.02/0.94  % SZS status Theorem for theBenchmark.p
% 4.02/0.94  
% 4.02/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.94  
% 4.02/0.94  fof(f17,conjecture,(
% 4.02/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f18,negated_conjecture,(
% 4.02/0.94    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 4.02/0.94    inference(negated_conjecture,[],[f17])).
% 4.02/0.94  
% 4.02/0.94  fof(f39,plain,(
% 4.02/0.94    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.02/0.94    inference(ennf_transformation,[],[f18])).
% 4.02/0.94  
% 4.02/0.94  fof(f42,plain,(
% 4.02/0.94    ( ! [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_xboole_0(k1_tops_1(X0,sK1),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.02/0.94    introduced(choice_axiom,[])).
% 4.02/0.94  
% 4.02/0.94  fof(f41,plain,(
% 4.02/0.94    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.02/0.94    introduced(choice_axiom,[])).
% 4.02/0.94  
% 4.02/0.94  fof(f43,plain,(
% 4.02/0.94    (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.02/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f42,f41])).
% 4.02/0.94  
% 4.02/0.94  fof(f63,plain,(
% 4.02/0.94    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.02/0.94    inference(cnf_transformation,[],[f43])).
% 4.02/0.94  
% 4.02/0.94  fof(f15,axiom,(
% 4.02/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f37,plain,(
% 4.02/0.94    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.02/0.94    inference(ennf_transformation,[],[f15])).
% 4.02/0.94  
% 4.02/0.94  fof(f60,plain,(
% 4.02/0.94    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.02/0.94    inference(cnf_transformation,[],[f37])).
% 4.02/0.94  
% 4.02/0.94  fof(f62,plain,(
% 4.02/0.94    l1_pre_topc(sK0)),
% 4.02/0.94    inference(cnf_transformation,[],[f43])).
% 4.02/0.94  
% 4.02/0.94  fof(f14,axiom,(
% 4.02/0.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f35,plain,(
% 4.02/0.94    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.02/0.94    inference(ennf_transformation,[],[f14])).
% 4.02/0.94  
% 4.02/0.94  fof(f36,plain,(
% 4.02/0.94    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.02/0.94    inference(flattening,[],[f35])).
% 4.02/0.94  
% 4.02/0.94  fof(f59,plain,(
% 4.02/0.94    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.02/0.94    inference(cnf_transformation,[],[f36])).
% 4.02/0.94  
% 4.02/0.94  fof(f8,axiom,(
% 4.02/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f26,plain,(
% 4.02/0.94    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.94    inference(ennf_transformation,[],[f8])).
% 4.02/0.94  
% 4.02/0.94  fof(f53,plain,(
% 4.02/0.94    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.94    inference(cnf_transformation,[],[f26])).
% 4.02/0.94  
% 4.02/0.94  fof(f6,axiom,(
% 4.02/0.94    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f24,plain,(
% 4.02/0.94    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.94    inference(ennf_transformation,[],[f6])).
% 4.02/0.94  
% 4.02/0.94  fof(f50,plain,(
% 4.02/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.94    inference(cnf_transformation,[],[f24])).
% 4.02/0.94  
% 4.02/0.94  fof(f2,axiom,(
% 4.02/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.94  
% 4.02/0.94  fof(f20,plain,(
% 4.02/0.94    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.94    inference(ennf_transformation,[],[f2])).
% 4.02/0.95  
% 4.02/0.95  fof(f46,plain,(
% 4.02/0.95    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f20])).
% 4.02/0.95  
% 4.02/0.95  fof(f16,axiom,(
% 4.02/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f38,plain,(
% 4.02/0.95    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.02/0.95    inference(ennf_transformation,[],[f16])).
% 4.02/0.95  
% 4.02/0.95  fof(f61,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.02/0.95    inference(cnf_transformation,[],[f38])).
% 4.02/0.95  
% 4.02/0.95  fof(f3,axiom,(
% 4.02/0.95    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f21,plain,(
% 4.02/0.95    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f3])).
% 4.02/0.95  
% 4.02/0.95  fof(f47,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f21])).
% 4.02/0.95  
% 4.02/0.95  fof(f5,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f23,plain,(
% 4.02/0.95    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f5])).
% 4.02/0.95  
% 4.02/0.95  fof(f49,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f23])).
% 4.02/0.95  
% 4.02/0.95  fof(f12,axiom,(
% 4.02/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f32,plain,(
% 4.02/0.95    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.02/0.95    inference(ennf_transformation,[],[f12])).
% 4.02/0.95  
% 4.02/0.95  fof(f57,plain,(
% 4.02/0.95    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.02/0.95    inference(cnf_transformation,[],[f32])).
% 4.02/0.95  
% 4.02/0.95  fof(f4,axiom,(
% 4.02/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f22,plain,(
% 4.02/0.95    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f4])).
% 4.02/0.95  
% 4.02/0.95  fof(f48,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f22])).
% 4.02/0.95  
% 4.02/0.95  fof(f9,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f27,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f9])).
% 4.02/0.95  
% 4.02/0.95  fof(f54,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f27])).
% 4.02/0.95  
% 4.02/0.95  fof(f7,axiom,(
% 4.02/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f25,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(ennf_transformation,[],[f7])).
% 4.02/0.95  
% 4.02/0.95  fof(f40,plain,(
% 4.02/0.95    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.02/0.95    inference(nnf_transformation,[],[f25])).
% 4.02/0.95  
% 4.02/0.95  fof(f52,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f40])).
% 4.02/0.95  
% 4.02/0.95  fof(f1,axiom,(
% 4.02/0.95    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.02/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/0.95  
% 4.02/0.95  fof(f19,plain,(
% 4.02/0.95    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 4.02/0.95    inference(ennf_transformation,[],[f1])).
% 4.02/0.95  
% 4.02/0.95  fof(f45,plain,(
% 4.02/0.95    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 4.02/0.95    inference(cnf_transformation,[],[f19])).
% 4.02/0.95  
% 4.02/0.95  fof(f64,plain,(
% 4.02/0.95    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 4.02/0.95    inference(cnf_transformation,[],[f43])).
% 4.02/0.95  
% 4.02/0.95  cnf(c_19,negated_conjecture,
% 4.02/0.95      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.02/0.95      inference(cnf_transformation,[],[f63]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_567,plain,
% 4.02/0.95      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_16,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.95      | ~ l1_pre_topc(X1)
% 4.02/0.95      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 4.02/0.95      inference(cnf_transformation,[],[f60]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_570,plain,
% 4.02/0.95      ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(X0) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_3057,plain,
% 4.02/0.95      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_570]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_20,negated_conjecture,
% 4.02/0.95      ( l1_pre_topc(sK0) ),
% 4.02/0.95      inference(cnf_transformation,[],[f62]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_807,plain,
% 4.02/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.02/0.95      | ~ l1_pre_topc(sK0)
% 4.02/0.95      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 4.02/0.95      inference(instantiation,[status(thm)],[c_16]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_4300,plain,
% 4.02/0.95      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 4.02/0.95      inference(global_propositional_subsumption,
% 4.02/0.95                [status(thm)],
% 4.02/0.95                [c_3057,c_20,c_19,c_807]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_15,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.95      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.95      | ~ l1_pre_topc(X1) ),
% 4.02/0.95      inference(cnf_transformation,[],[f59]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_571,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.02/0.95      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.02/0.95      | l1_pre_topc(X1) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_4303,plain,
% 4.02/0.95      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.02/0.95      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_4300,c_571]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_21,plain,
% 4.02/0.95      ( l1_pre_topc(sK0) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_22,plain,
% 4.02/0.95      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_799,plain,
% 4.02/0.95      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.02/0.95      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.02/0.95      | ~ l1_pre_topc(sK0) ),
% 4.02/0.95      inference(instantiation,[status(thm)],[c_15]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_800,plain,
% 4.02/0.95      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.02/0.95      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_5651,plain,
% 4.02/0.95      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.02/0.95      inference(global_propositional_subsumption,
% 4.02/0.95                [status(thm)],
% 4.02/0.95                [c_4303,c_21,c_22,c_800]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_9,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.02/0.95      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f53]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_577,plain,
% 4.02/0.95      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.02/0.95      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_6319,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
% 4.02/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_577]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_6,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.02/0.95      inference(cnf_transformation,[],[f50]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_580,plain,
% 4.02/0.95      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_1279,plain,
% 4.02/0.95      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_580]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_6343,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
% 4.02/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.02/0.95      inference(light_normalisation,[status(thm)],[c_6319,c_1279]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_6988,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_5651,c_6343]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_2,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f46]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_584,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_17,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.95      | ~ l1_pre_topc(X1)
% 4.02/0.95      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 4.02/0.95      inference(cnf_transformation,[],[f61]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_569,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(X0) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_1592,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(X0) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_584,c_569]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_8274,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_1592]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_8297,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(light_normalisation,[status(thm)],[c_8274,c_4300]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_9338,plain,
% 4.02/0.95      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 4.02/0.95      inference(global_propositional_subsumption,
% 4.02/0.95                [status(thm)],
% 4.02/0.95                [c_8297,c_21]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_11789,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 4.02/0.95      inference(light_normalisation,[status(thm)],[c_6988,c_9338]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_3,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f47]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_583,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_2495,plain,
% 4.02/0.95      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.02/0.95      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_1279,c_583]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_2775,plain,
% 4.02/0.95      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.02/0.95      inference(global_propositional_subsumption,
% 4.02/0.95                [status(thm)],
% 4.02/0.95                [c_2495,c_22]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_5,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.02/0.95      inference(cnf_transformation,[],[f49]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_581,plain,
% 4.02/0.95      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_2784,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,X0) ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_2775,c_581]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_11803,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_11789,c_2784]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_13,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.95      | ~ l1_pre_topc(X1)
% 4.02/0.95      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 4.02/0.95      inference(cnf_transformation,[],[f57]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_573,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 4.02/0.95      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.02/0.95      | l1_pre_topc(X0) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_3773,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1)
% 4.02/0.95      | l1_pre_topc(sK0) != iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_573]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_836,plain,
% 4.02/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.02/0.95      | ~ l1_pre_topc(sK0)
% 4.02/0.95      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 4.02/0.95      inference(instantiation,[status(thm)],[c_13]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_4306,plain,
% 4.02/0.95      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 4.02/0.95      inference(global_propositional_subsumption,
% 4.02/0.95                [status(thm)],
% 4.02/0.95                [c_3773,c_20,c_19,c_836]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_11805,plain,
% 4.02/0.95      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 4.02/0.95      inference(light_normalisation,[status(thm)],[c_11803,c_4306]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_4,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 4.02/0.95      inference(cnf_transformation,[],[f48]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_582,plain,
% 4.02/0.95      ( k9_subset_1(X0,X1,X1) = X1
% 4.02/0.95      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_820,plain,
% 4.02/0.95      ( k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_567,c_582]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_10,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.02/0.95      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
% 4.02/0.95      inference(cnf_transformation,[],[f54]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_576,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_3846,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.02/0.95      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_820,c_576]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_7,plain,
% 4.02/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.02/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.02/0.95      | r1_tarski(X0,X2)
% 4.02/0.95      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f52]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_579,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.02/0.95      | r1_tarski(X0,X2) = iProver_top
% 4.02/0.95      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_6711,plain,
% 4.02/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.02/0.95      | r1_tarski(X0,X0) = iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_3846,c_579]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_9055,plain,
% 4.02/0.95      ( r1_tarski(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0)) = iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_2775,c_6711]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_0,plain,
% 4.02/0.95      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 4.02/0.95      inference(cnf_transformation,[],[f45]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_586,plain,
% 4.02/0.95      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 4.02/0.95      | r1_xboole_0(X0,X2) = iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_11404,plain,
% 4.02/0.95      ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) = iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_9055,c_586]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_12482,plain,
% 4.02/0.95      ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.02/0.95      inference(superposition,[status(thm)],[c_11805,c_11404]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_18,negated_conjecture,
% 4.02/0.95      ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 4.02/0.95      inference(cnf_transformation,[],[f64]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(c_23,plain,
% 4.02/0.95      ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
% 4.02/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.02/0.95  
% 4.02/0.95  cnf(contradiction,plain,
% 4.02/0.95      ( $false ),
% 4.02/0.95      inference(minisat,[status(thm)],[c_12482,c_23]) ).
% 4.02/0.95  
% 4.02/0.95  
% 4.02/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.95  
% 4.02/0.95  ------                               Statistics
% 4.02/0.95  
% 4.02/0.95  ------ Selected
% 4.02/0.95  
% 4.02/0.95  total_time:                             0.423
% 4.02/0.95  
%------------------------------------------------------------------------------
