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
% DateTime   : Thu Dec  3 11:54:49 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 190 expanded)
%              Number of clauses        :   50 (  78 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  223 ( 570 expanded)
%              Number of equality atoms :   66 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f23])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_4])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_257,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_167,c_14])).

cnf(c_258,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_537,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_714,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_537])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_209,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_210,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_540,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_646,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_540])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_748,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_749,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_1010,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_646,c_749])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_544,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1015,plain,
    ( k2_xboole_0(k1_relat_1(sK4),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_1010,c_544])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_545,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1207,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_545])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_242,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_186,c_14])).

cnf(c_243,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_538,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
    | r1_tarski(k2_relat_1(sK4),X1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_720,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_538])).

cnf(c_1060,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_646,c_749])).

cnf(c_1065,plain,
    ( k2_xboole_0(k2_relat_1(sK4),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1060,c_544])).

cnf(c_1210,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_545])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,negated_conjecture,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_224,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_225,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ r1_tarski(k1_relat_1(sK4),X1)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_539,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_226,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_778,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_226,c_646,c_749])).

cnf(c_779,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_787,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_779])).

cnf(c_1377,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_787])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1802,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1377,c_17])).

cnf(c_1808,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1802])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1808,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.15/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.15/1.06  
% 1.15/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.15/1.06  
% 1.15/1.06  ------  iProver source info
% 1.15/1.06  
% 1.15/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.15/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.15/1.06  git: non_committed_changes: false
% 1.15/1.06  git: last_make_outside_of_git: false
% 1.15/1.06  
% 1.15/1.06  ------ 
% 1.15/1.06  
% 1.15/1.06  ------ Input Options
% 1.15/1.06  
% 1.15/1.06  --out_options                           all
% 1.15/1.06  --tptp_safe_out                         true
% 1.15/1.06  --problem_path                          ""
% 1.15/1.06  --include_path                          ""
% 1.15/1.06  --clausifier                            res/vclausify_rel
% 1.15/1.06  --clausifier_options                    --mode clausify
% 1.15/1.06  --stdin                                 false
% 1.15/1.06  --stats_out                             all
% 1.15/1.06  
% 1.15/1.06  ------ General Options
% 1.15/1.06  
% 1.15/1.06  --fof                                   false
% 1.15/1.06  --time_out_real                         305.
% 1.15/1.06  --time_out_virtual                      -1.
% 1.15/1.06  --symbol_type_check                     false
% 1.15/1.06  --clausify_out                          false
% 1.15/1.06  --sig_cnt_out                           false
% 1.15/1.06  --trig_cnt_out                          false
% 1.15/1.06  --trig_cnt_out_tolerance                1.
% 1.15/1.06  --trig_cnt_out_sk_spl                   false
% 1.15/1.06  --abstr_cl_out                          false
% 1.15/1.06  
% 1.15/1.06  ------ Global Options
% 1.15/1.06  
% 1.15/1.06  --schedule                              default
% 1.15/1.06  --add_important_lit                     false
% 1.15/1.06  --prop_solver_per_cl                    1000
% 1.15/1.06  --min_unsat_core                        false
% 1.15/1.06  --soft_assumptions                      false
% 1.15/1.06  --soft_lemma_size                       3
% 1.15/1.06  --prop_impl_unit_size                   0
% 1.15/1.06  --prop_impl_unit                        []
% 1.15/1.06  --share_sel_clauses                     true
% 1.15/1.06  --reset_solvers                         false
% 1.15/1.06  --bc_imp_inh                            [conj_cone]
% 1.15/1.06  --conj_cone_tolerance                   3.
% 1.15/1.06  --extra_neg_conj                        none
% 1.15/1.06  --large_theory_mode                     true
% 1.15/1.06  --prolific_symb_bound                   200
% 1.15/1.06  --lt_threshold                          2000
% 1.15/1.06  --clause_weak_htbl                      true
% 1.15/1.06  --gc_record_bc_elim                     false
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing Options
% 1.15/1.06  
% 1.15/1.06  --preprocessing_flag                    true
% 1.15/1.06  --time_out_prep_mult                    0.1
% 1.15/1.06  --splitting_mode                        input
% 1.15/1.06  --splitting_grd                         true
% 1.15/1.06  --splitting_cvd                         false
% 1.15/1.06  --splitting_cvd_svl                     false
% 1.15/1.06  --splitting_nvd                         32
% 1.15/1.06  --sub_typing                            true
% 1.15/1.06  --prep_gs_sim                           true
% 1.15/1.06  --prep_unflatten                        true
% 1.15/1.06  --prep_res_sim                          true
% 1.15/1.06  --prep_upred                            true
% 1.15/1.06  --prep_sem_filter                       exhaustive
% 1.15/1.06  --prep_sem_filter_out                   false
% 1.15/1.06  --pred_elim                             true
% 1.15/1.06  --res_sim_input                         true
% 1.15/1.06  --eq_ax_congr_red                       true
% 1.15/1.06  --pure_diseq_elim                       true
% 1.15/1.06  --brand_transform                       false
% 1.15/1.06  --non_eq_to_eq                          false
% 1.15/1.06  --prep_def_merge                        true
% 1.15/1.06  --prep_def_merge_prop_impl              false
% 1.15/1.06  --prep_def_merge_mbd                    true
% 1.15/1.06  --prep_def_merge_tr_red                 false
% 1.15/1.06  --prep_def_merge_tr_cl                  false
% 1.15/1.06  --smt_preprocessing                     true
% 1.15/1.06  --smt_ac_axioms                         fast
% 1.15/1.06  --preprocessed_out                      false
% 1.15/1.06  --preprocessed_stats                    false
% 1.15/1.06  
% 1.15/1.06  ------ Abstraction refinement Options
% 1.15/1.06  
% 1.15/1.06  --abstr_ref                             []
% 1.15/1.06  --abstr_ref_prep                        false
% 1.15/1.06  --abstr_ref_until_sat                   false
% 1.15/1.06  --abstr_ref_sig_restrict                funpre
% 1.15/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.15/1.06  --abstr_ref_under                       []
% 1.15/1.06  
% 1.15/1.06  ------ SAT Options
% 1.15/1.06  
% 1.15/1.06  --sat_mode                              false
% 1.15/1.06  --sat_fm_restart_options                ""
% 1.15/1.06  --sat_gr_def                            false
% 1.15/1.06  --sat_epr_types                         true
% 1.15/1.06  --sat_non_cyclic_types                  false
% 1.15/1.06  --sat_finite_models                     false
% 1.15/1.06  --sat_fm_lemmas                         false
% 1.15/1.06  --sat_fm_prep                           false
% 1.15/1.06  --sat_fm_uc_incr                        true
% 1.15/1.06  --sat_out_model                         small
% 1.15/1.06  --sat_out_clauses                       false
% 1.15/1.06  
% 1.15/1.06  ------ QBF Options
% 1.15/1.06  
% 1.15/1.06  --qbf_mode                              false
% 1.15/1.06  --qbf_elim_univ                         false
% 1.15/1.06  --qbf_dom_inst                          none
% 1.15/1.06  --qbf_dom_pre_inst                      false
% 1.15/1.06  --qbf_sk_in                             false
% 1.15/1.06  --qbf_pred_elim                         true
% 1.15/1.06  --qbf_split                             512
% 1.15/1.06  
% 1.15/1.06  ------ BMC1 Options
% 1.15/1.06  
% 1.15/1.06  --bmc1_incremental                      false
% 1.15/1.06  --bmc1_axioms                           reachable_all
% 1.15/1.06  --bmc1_min_bound                        0
% 1.15/1.06  --bmc1_max_bound                        -1
% 1.15/1.06  --bmc1_max_bound_default                -1
% 1.15/1.06  --bmc1_symbol_reachability              true
% 1.15/1.06  --bmc1_property_lemmas                  false
% 1.15/1.06  --bmc1_k_induction                      false
% 1.15/1.06  --bmc1_non_equiv_states                 false
% 1.15/1.06  --bmc1_deadlock                         false
% 1.15/1.06  --bmc1_ucm                              false
% 1.15/1.06  --bmc1_add_unsat_core                   none
% 1.15/1.06  --bmc1_unsat_core_children              false
% 1.15/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.15/1.06  --bmc1_out_stat                         full
% 1.15/1.06  --bmc1_ground_init                      false
% 1.15/1.06  --bmc1_pre_inst_next_state              false
% 1.15/1.06  --bmc1_pre_inst_state                   false
% 1.15/1.06  --bmc1_pre_inst_reach_state             false
% 1.15/1.06  --bmc1_out_unsat_core                   false
% 1.15/1.06  --bmc1_aig_witness_out                  false
% 1.15/1.06  --bmc1_verbose                          false
% 1.15/1.06  --bmc1_dump_clauses_tptp                false
% 1.15/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.15/1.06  --bmc1_dump_file                        -
% 1.15/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.15/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.15/1.06  --bmc1_ucm_extend_mode                  1
% 1.15/1.06  --bmc1_ucm_init_mode                    2
% 1.15/1.06  --bmc1_ucm_cone_mode                    none
% 1.15/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.15/1.06  --bmc1_ucm_relax_model                  4
% 1.15/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.15/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.15/1.06  --bmc1_ucm_layered_model                none
% 1.15/1.06  --bmc1_ucm_max_lemma_size               10
% 1.15/1.06  
% 1.15/1.06  ------ AIG Options
% 1.15/1.06  
% 1.15/1.06  --aig_mode                              false
% 1.15/1.06  
% 1.15/1.06  ------ Instantiation Options
% 1.15/1.06  
% 1.15/1.06  --instantiation_flag                    true
% 1.15/1.06  --inst_sos_flag                         false
% 1.15/1.06  --inst_sos_phase                        true
% 1.15/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.15/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.15/1.06  --inst_lit_sel_side                     num_symb
% 1.15/1.06  --inst_solver_per_active                1400
% 1.15/1.06  --inst_solver_calls_frac                1.
% 1.15/1.06  --inst_passive_queue_type               priority_queues
% 1.15/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.15/1.06  --inst_passive_queues_freq              [25;2]
% 1.15/1.06  --inst_dismatching                      true
% 1.15/1.06  --inst_eager_unprocessed_to_passive     true
% 1.15/1.06  --inst_prop_sim_given                   true
% 1.15/1.06  --inst_prop_sim_new                     false
% 1.15/1.06  --inst_subs_new                         false
% 1.15/1.06  --inst_eq_res_simp                      false
% 1.15/1.06  --inst_subs_given                       false
% 1.15/1.06  --inst_orphan_elimination               true
% 1.15/1.06  --inst_learning_loop_flag               true
% 1.15/1.06  --inst_learning_start                   3000
% 1.15/1.06  --inst_learning_factor                  2
% 1.15/1.06  --inst_start_prop_sim_after_learn       3
% 1.15/1.06  --inst_sel_renew                        solver
% 1.15/1.06  --inst_lit_activity_flag                true
% 1.15/1.06  --inst_restr_to_given                   false
% 1.15/1.06  --inst_activity_threshold               500
% 1.15/1.06  --inst_out_proof                        true
% 1.15/1.06  
% 1.15/1.06  ------ Resolution Options
% 1.15/1.06  
% 1.15/1.06  --resolution_flag                       true
% 1.15/1.06  --res_lit_sel                           adaptive
% 1.15/1.06  --res_lit_sel_side                      none
% 1.15/1.06  --res_ordering                          kbo
% 1.15/1.06  --res_to_prop_solver                    active
% 1.15/1.06  --res_prop_simpl_new                    false
% 1.15/1.06  --res_prop_simpl_given                  true
% 1.15/1.06  --res_passive_queue_type                priority_queues
% 1.15/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.15/1.06  --res_passive_queues_freq               [15;5]
% 1.15/1.06  --res_forward_subs                      full
% 1.15/1.06  --res_backward_subs                     full
% 1.15/1.06  --res_forward_subs_resolution           true
% 1.15/1.06  --res_backward_subs_resolution          true
% 1.15/1.06  --res_orphan_elimination                true
% 1.15/1.06  --res_time_limit                        2.
% 1.15/1.06  --res_out_proof                         true
% 1.15/1.06  
% 1.15/1.06  ------ Superposition Options
% 1.15/1.06  
% 1.15/1.06  --superposition_flag                    true
% 1.15/1.06  --sup_passive_queue_type                priority_queues
% 1.15/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.15/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.15/1.06  --demod_completeness_check              fast
% 1.15/1.06  --demod_use_ground                      true
% 1.15/1.06  --sup_to_prop_solver                    passive
% 1.15/1.06  --sup_prop_simpl_new                    true
% 1.15/1.06  --sup_prop_simpl_given                  true
% 1.15/1.06  --sup_fun_splitting                     false
% 1.15/1.06  --sup_smt_interval                      50000
% 1.15/1.06  
% 1.15/1.06  ------ Superposition Simplification Setup
% 1.15/1.06  
% 1.15/1.06  --sup_indices_passive                   []
% 1.15/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.15/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_full_bw                           [BwDemod]
% 1.15/1.06  --sup_immed_triv                        [TrivRules]
% 1.15/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.15/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_immed_bw_main                     []
% 1.15/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.15/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.06  
% 1.15/1.06  ------ Combination Options
% 1.15/1.06  
% 1.15/1.06  --comb_res_mult                         3
% 1.15/1.06  --comb_sup_mult                         2
% 1.15/1.06  --comb_inst_mult                        10
% 1.15/1.06  
% 1.15/1.06  ------ Debug Options
% 1.15/1.06  
% 1.15/1.06  --dbg_backtrace                         false
% 1.15/1.06  --dbg_dump_prop_clauses                 false
% 1.15/1.06  --dbg_dump_prop_clauses_file            -
% 1.15/1.06  --dbg_out_stat                          false
% 1.15/1.06  ------ Parsing...
% 1.15/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.15/1.06  ------ Proving...
% 1.15/1.06  ------ Problem Properties 
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  clauses                                 10
% 1.15/1.06  conjectures                             2
% 1.15/1.06  EPR                                     2
% 1.15/1.06  Horn                                    10
% 1.15/1.06  unary                                   4
% 1.15/1.06  binary                                  2
% 1.15/1.06  lits                                    21
% 1.15/1.06  lits eq                                 6
% 1.15/1.06  fd_pure                                 0
% 1.15/1.06  fd_pseudo                               0
% 1.15/1.06  fd_cond                                 0
% 1.15/1.06  fd_pseudo_cond                          0
% 1.15/1.06  AC symbols                              0
% 1.15/1.06  
% 1.15/1.06  ------ Schedule dynamic 5 is on 
% 1.15/1.06  
% 1.15/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  ------ 
% 1.15/1.06  Current options:
% 1.15/1.06  ------ 
% 1.15/1.06  
% 1.15/1.06  ------ Input Options
% 1.15/1.06  
% 1.15/1.06  --out_options                           all
% 1.15/1.06  --tptp_safe_out                         true
% 1.15/1.06  --problem_path                          ""
% 1.15/1.06  --include_path                          ""
% 1.15/1.06  --clausifier                            res/vclausify_rel
% 1.15/1.06  --clausifier_options                    --mode clausify
% 1.15/1.06  --stdin                                 false
% 1.15/1.06  --stats_out                             all
% 1.15/1.06  
% 1.15/1.06  ------ General Options
% 1.15/1.06  
% 1.15/1.06  --fof                                   false
% 1.15/1.06  --time_out_real                         305.
% 1.15/1.06  --time_out_virtual                      -1.
% 1.15/1.06  --symbol_type_check                     false
% 1.15/1.06  --clausify_out                          false
% 1.15/1.06  --sig_cnt_out                           false
% 1.15/1.06  --trig_cnt_out                          false
% 1.15/1.06  --trig_cnt_out_tolerance                1.
% 1.15/1.06  --trig_cnt_out_sk_spl                   false
% 1.15/1.06  --abstr_cl_out                          false
% 1.15/1.06  
% 1.15/1.06  ------ Global Options
% 1.15/1.06  
% 1.15/1.06  --schedule                              default
% 1.15/1.06  --add_important_lit                     false
% 1.15/1.06  --prop_solver_per_cl                    1000
% 1.15/1.06  --min_unsat_core                        false
% 1.15/1.06  --soft_assumptions                      false
% 1.15/1.06  --soft_lemma_size                       3
% 1.15/1.06  --prop_impl_unit_size                   0
% 1.15/1.06  --prop_impl_unit                        []
% 1.15/1.06  --share_sel_clauses                     true
% 1.15/1.06  --reset_solvers                         false
% 1.15/1.06  --bc_imp_inh                            [conj_cone]
% 1.15/1.06  --conj_cone_tolerance                   3.
% 1.15/1.06  --extra_neg_conj                        none
% 1.15/1.06  --large_theory_mode                     true
% 1.15/1.06  --prolific_symb_bound                   200
% 1.15/1.06  --lt_threshold                          2000
% 1.15/1.06  --clause_weak_htbl                      true
% 1.15/1.06  --gc_record_bc_elim                     false
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing Options
% 1.15/1.06  
% 1.15/1.06  --preprocessing_flag                    true
% 1.15/1.06  --time_out_prep_mult                    0.1
% 1.15/1.06  --splitting_mode                        input
% 1.15/1.06  --splitting_grd                         true
% 1.15/1.06  --splitting_cvd                         false
% 1.15/1.06  --splitting_cvd_svl                     false
% 1.15/1.06  --splitting_nvd                         32
% 1.15/1.06  --sub_typing                            true
% 1.15/1.06  --prep_gs_sim                           true
% 1.15/1.06  --prep_unflatten                        true
% 1.15/1.06  --prep_res_sim                          true
% 1.15/1.06  --prep_upred                            true
% 1.15/1.06  --prep_sem_filter                       exhaustive
% 1.15/1.06  --prep_sem_filter_out                   false
% 1.15/1.06  --pred_elim                             true
% 1.15/1.06  --res_sim_input                         true
% 1.15/1.06  --eq_ax_congr_red                       true
% 1.15/1.06  --pure_diseq_elim                       true
% 1.15/1.06  --brand_transform                       false
% 1.15/1.06  --non_eq_to_eq                          false
% 1.15/1.06  --prep_def_merge                        true
% 1.15/1.06  --prep_def_merge_prop_impl              false
% 1.15/1.06  --prep_def_merge_mbd                    true
% 1.15/1.06  --prep_def_merge_tr_red                 false
% 1.15/1.06  --prep_def_merge_tr_cl                  false
% 1.15/1.06  --smt_preprocessing                     true
% 1.15/1.06  --smt_ac_axioms                         fast
% 1.15/1.06  --preprocessed_out                      false
% 1.15/1.06  --preprocessed_stats                    false
% 1.15/1.06  
% 1.15/1.06  ------ Abstraction refinement Options
% 1.15/1.06  
% 1.15/1.06  --abstr_ref                             []
% 1.15/1.06  --abstr_ref_prep                        false
% 1.15/1.06  --abstr_ref_until_sat                   false
% 1.15/1.06  --abstr_ref_sig_restrict                funpre
% 1.15/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.15/1.06  --abstr_ref_under                       []
% 1.15/1.06  
% 1.15/1.06  ------ SAT Options
% 1.15/1.06  
% 1.15/1.06  --sat_mode                              false
% 1.15/1.06  --sat_fm_restart_options                ""
% 1.15/1.06  --sat_gr_def                            false
% 1.15/1.06  --sat_epr_types                         true
% 1.15/1.06  --sat_non_cyclic_types                  false
% 1.15/1.06  --sat_finite_models                     false
% 1.15/1.06  --sat_fm_lemmas                         false
% 1.15/1.06  --sat_fm_prep                           false
% 1.15/1.06  --sat_fm_uc_incr                        true
% 1.15/1.06  --sat_out_model                         small
% 1.15/1.06  --sat_out_clauses                       false
% 1.15/1.06  
% 1.15/1.06  ------ QBF Options
% 1.15/1.06  
% 1.15/1.06  --qbf_mode                              false
% 1.15/1.06  --qbf_elim_univ                         false
% 1.15/1.06  --qbf_dom_inst                          none
% 1.15/1.06  --qbf_dom_pre_inst                      false
% 1.15/1.06  --qbf_sk_in                             false
% 1.15/1.06  --qbf_pred_elim                         true
% 1.15/1.06  --qbf_split                             512
% 1.15/1.06  
% 1.15/1.06  ------ BMC1 Options
% 1.15/1.06  
% 1.15/1.06  --bmc1_incremental                      false
% 1.15/1.06  --bmc1_axioms                           reachable_all
% 1.15/1.06  --bmc1_min_bound                        0
% 1.15/1.06  --bmc1_max_bound                        -1
% 1.15/1.06  --bmc1_max_bound_default                -1
% 1.15/1.06  --bmc1_symbol_reachability              true
% 1.15/1.06  --bmc1_property_lemmas                  false
% 1.15/1.06  --bmc1_k_induction                      false
% 1.15/1.06  --bmc1_non_equiv_states                 false
% 1.15/1.06  --bmc1_deadlock                         false
% 1.15/1.06  --bmc1_ucm                              false
% 1.15/1.06  --bmc1_add_unsat_core                   none
% 1.15/1.06  --bmc1_unsat_core_children              false
% 1.15/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.15/1.06  --bmc1_out_stat                         full
% 1.15/1.06  --bmc1_ground_init                      false
% 1.15/1.06  --bmc1_pre_inst_next_state              false
% 1.15/1.06  --bmc1_pre_inst_state                   false
% 1.15/1.06  --bmc1_pre_inst_reach_state             false
% 1.15/1.06  --bmc1_out_unsat_core                   false
% 1.15/1.06  --bmc1_aig_witness_out                  false
% 1.15/1.06  --bmc1_verbose                          false
% 1.15/1.06  --bmc1_dump_clauses_tptp                false
% 1.15/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.15/1.06  --bmc1_dump_file                        -
% 1.15/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.15/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.15/1.06  --bmc1_ucm_extend_mode                  1
% 1.15/1.06  --bmc1_ucm_init_mode                    2
% 1.15/1.06  --bmc1_ucm_cone_mode                    none
% 1.15/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.15/1.06  --bmc1_ucm_relax_model                  4
% 1.15/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.15/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.15/1.06  --bmc1_ucm_layered_model                none
% 1.15/1.06  --bmc1_ucm_max_lemma_size               10
% 1.15/1.06  
% 1.15/1.06  ------ AIG Options
% 1.15/1.06  
% 1.15/1.06  --aig_mode                              false
% 1.15/1.06  
% 1.15/1.06  ------ Instantiation Options
% 1.15/1.06  
% 1.15/1.06  --instantiation_flag                    true
% 1.15/1.06  --inst_sos_flag                         false
% 1.15/1.06  --inst_sos_phase                        true
% 1.15/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.15/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.15/1.06  --inst_lit_sel_side                     none
% 1.15/1.06  --inst_solver_per_active                1400
% 1.15/1.06  --inst_solver_calls_frac                1.
% 1.15/1.06  --inst_passive_queue_type               priority_queues
% 1.15/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.15/1.06  --inst_passive_queues_freq              [25;2]
% 1.15/1.06  --inst_dismatching                      true
% 1.15/1.06  --inst_eager_unprocessed_to_passive     true
% 1.15/1.06  --inst_prop_sim_given                   true
% 1.15/1.06  --inst_prop_sim_new                     false
% 1.15/1.06  --inst_subs_new                         false
% 1.15/1.06  --inst_eq_res_simp                      false
% 1.15/1.06  --inst_subs_given                       false
% 1.15/1.06  --inst_orphan_elimination               true
% 1.15/1.06  --inst_learning_loop_flag               true
% 1.15/1.06  --inst_learning_start                   3000
% 1.15/1.06  --inst_learning_factor                  2
% 1.15/1.06  --inst_start_prop_sim_after_learn       3
% 1.15/1.06  --inst_sel_renew                        solver
% 1.15/1.06  --inst_lit_activity_flag                true
% 1.15/1.06  --inst_restr_to_given                   false
% 1.15/1.06  --inst_activity_threshold               500
% 1.15/1.06  --inst_out_proof                        true
% 1.15/1.06  
% 1.15/1.06  ------ Resolution Options
% 1.15/1.06  
% 1.15/1.06  --resolution_flag                       false
% 1.15/1.06  --res_lit_sel                           adaptive
% 1.15/1.06  --res_lit_sel_side                      none
% 1.15/1.06  --res_ordering                          kbo
% 1.15/1.06  --res_to_prop_solver                    active
% 1.15/1.06  --res_prop_simpl_new                    false
% 1.15/1.06  --res_prop_simpl_given                  true
% 1.15/1.06  --res_passive_queue_type                priority_queues
% 1.15/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.15/1.06  --res_passive_queues_freq               [15;5]
% 1.15/1.06  --res_forward_subs                      full
% 1.15/1.06  --res_backward_subs                     full
% 1.15/1.06  --res_forward_subs_resolution           true
% 1.15/1.06  --res_backward_subs_resolution          true
% 1.15/1.06  --res_orphan_elimination                true
% 1.15/1.06  --res_time_limit                        2.
% 1.15/1.06  --res_out_proof                         true
% 1.15/1.06  
% 1.15/1.06  ------ Superposition Options
% 1.15/1.06  
% 1.15/1.06  --superposition_flag                    true
% 1.15/1.06  --sup_passive_queue_type                priority_queues
% 1.15/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.15/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.15/1.06  --demod_completeness_check              fast
% 1.15/1.06  --demod_use_ground                      true
% 1.15/1.06  --sup_to_prop_solver                    passive
% 1.15/1.06  --sup_prop_simpl_new                    true
% 1.15/1.06  --sup_prop_simpl_given                  true
% 1.15/1.06  --sup_fun_splitting                     false
% 1.15/1.06  --sup_smt_interval                      50000
% 1.15/1.06  
% 1.15/1.06  ------ Superposition Simplification Setup
% 1.15/1.06  
% 1.15/1.06  --sup_indices_passive                   []
% 1.15/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.15/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_full_bw                           [BwDemod]
% 1.15/1.06  --sup_immed_triv                        [TrivRules]
% 1.15/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.15/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_immed_bw_main                     []
% 1.15/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.15/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.06  
% 1.15/1.06  ------ Combination Options
% 1.15/1.06  
% 1.15/1.06  --comb_res_mult                         3
% 1.15/1.06  --comb_sup_mult                         2
% 1.15/1.06  --comb_inst_mult                        10
% 1.15/1.06  
% 1.15/1.06  ------ Debug Options
% 1.15/1.06  
% 1.15/1.06  --dbg_backtrace                         false
% 1.15/1.06  --dbg_dump_prop_clauses                 false
% 1.15/1.06  --dbg_dump_prop_clauses_file            -
% 1.15/1.06  --dbg_out_stat                          false
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  ------ Proving...
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  % SZS status Theorem for theBenchmark.p
% 1.15/1.06  
% 1.15/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.15/1.06  
% 1.15/1.06  fof(f7,axiom,(
% 1.15/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f16,plain,(
% 1.15/1.06    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.15/1.06    inference(ennf_transformation,[],[f7])).
% 1.15/1.06  
% 1.15/1.06  fof(f33,plain,(
% 1.15/1.06    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/1.06    inference(cnf_transformation,[],[f16])).
% 1.15/1.06  
% 1.15/1.06  fof(f4,axiom,(
% 1.15/1.06    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f14,plain,(
% 1.15/1.06    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.15/1.06    inference(ennf_transformation,[],[f4])).
% 1.15/1.06  
% 1.15/1.06  fof(f21,plain,(
% 1.15/1.06    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.15/1.06    inference(nnf_transformation,[],[f14])).
% 1.15/1.06  
% 1.15/1.06  fof(f28,plain,(
% 1.15/1.06    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f21])).
% 1.15/1.06  
% 1.15/1.06  fof(f9,conjecture,(
% 1.15/1.06    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f10,negated_conjecture,(
% 1.15/1.06    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 1.15/1.06    inference(negated_conjecture,[],[f9])).
% 1.15/1.06  
% 1.15/1.06  fof(f19,plain,(
% 1.15/1.06    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.15/1.06    inference(ennf_transformation,[],[f10])).
% 1.15/1.06  
% 1.15/1.06  fof(f20,plain,(
% 1.15/1.06    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.15/1.06    inference(flattening,[],[f19])).
% 1.15/1.06  
% 1.15/1.06  fof(f23,plain,(
% 1.15/1.06    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 1.15/1.06    introduced(choice_axiom,[])).
% 1.15/1.06  
% 1.15/1.06  fof(f24,plain,(
% 1.15/1.06    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.15/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f23])).
% 1.15/1.06  
% 1.15/1.06  fof(f36,plain,(
% 1.15/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.15/1.06    inference(cnf_transformation,[],[f24])).
% 1.15/1.06  
% 1.15/1.06  fof(f3,axiom,(
% 1.15/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f13,plain,(
% 1.15/1.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.15/1.06    inference(ennf_transformation,[],[f3])).
% 1.15/1.06  
% 1.15/1.06  fof(f27,plain,(
% 1.15/1.06    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f13])).
% 1.15/1.06  
% 1.15/1.06  fof(f6,axiom,(
% 1.15/1.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f32,plain,(
% 1.15/1.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.15/1.06    inference(cnf_transformation,[],[f6])).
% 1.15/1.06  
% 1.15/1.06  fof(f2,axiom,(
% 1.15/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f12,plain,(
% 1.15/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.15/1.06    inference(ennf_transformation,[],[f2])).
% 1.15/1.06  
% 1.15/1.06  fof(f26,plain,(
% 1.15/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f12])).
% 1.15/1.06  
% 1.15/1.06  fof(f1,axiom,(
% 1.15/1.06    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f11,plain,(
% 1.15/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.15/1.06    inference(ennf_transformation,[],[f1])).
% 1.15/1.06  
% 1.15/1.06  fof(f25,plain,(
% 1.15/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f11])).
% 1.15/1.06  
% 1.15/1.06  fof(f34,plain,(
% 1.15/1.06    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/1.06    inference(cnf_transformation,[],[f16])).
% 1.15/1.06  
% 1.15/1.06  fof(f5,axiom,(
% 1.15/1.06    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f15,plain,(
% 1.15/1.06    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.15/1.06    inference(ennf_transformation,[],[f5])).
% 1.15/1.06  
% 1.15/1.06  fof(f22,plain,(
% 1.15/1.06    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.15/1.06    inference(nnf_transformation,[],[f15])).
% 1.15/1.06  
% 1.15/1.06  fof(f30,plain,(
% 1.15/1.06    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f22])).
% 1.15/1.06  
% 1.15/1.06  fof(f8,axiom,(
% 1.15/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.15/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.15/1.06  
% 1.15/1.06  fof(f17,plain,(
% 1.15/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.15/1.06    inference(ennf_transformation,[],[f8])).
% 1.15/1.06  
% 1.15/1.06  fof(f18,plain,(
% 1.15/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.15/1.06    inference(flattening,[],[f17])).
% 1.15/1.06  
% 1.15/1.06  fof(f35,plain,(
% 1.15/1.06    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.15/1.06    inference(cnf_transformation,[],[f18])).
% 1.15/1.06  
% 1.15/1.06  fof(f39,plain,(
% 1.15/1.06    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.15/1.06    inference(cnf_transformation,[],[f24])).
% 1.15/1.06  
% 1.15/1.06  fof(f38,plain,(
% 1.15/1.06    r1_tarski(sK2,sK3)),
% 1.15/1.06    inference(cnf_transformation,[],[f24])).
% 1.15/1.06  
% 1.15/1.06  fof(f37,plain,(
% 1.15/1.06    r1_tarski(sK0,sK1)),
% 1.15/1.06    inference(cnf_transformation,[],[f24])).
% 1.15/1.06  
% 1.15/1.06  cnf(c_9,plain,
% 1.15/1.06      ( v4_relat_1(X0,X1)
% 1.15/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.15/1.06      inference(cnf_transformation,[],[f33]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_4,plain,
% 1.15/1.06      ( ~ v4_relat_1(X0,X1)
% 1.15/1.06      | r1_tarski(k1_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0) ),
% 1.15/1.06      inference(cnf_transformation,[],[f28]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_167,plain,
% 1.15/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.15/1.06      | r1_tarski(k1_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0) ),
% 1.15/1.06      inference(resolution,[status(thm)],[c_9,c_4]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_14,negated_conjecture,
% 1.15/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 1.15/1.06      inference(cnf_transformation,[],[f36]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_257,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.15/1.06      | sK4 != X0 ),
% 1.15/1.06      inference(resolution_lifted,[status(thm)],[c_167,c_14]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_258,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),X0)
% 1.15/1.06      | ~ v1_relat_1(sK4)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 1.15/1.06      inference(unflattening,[status(thm)],[c_257]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_537,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.15/1.06      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_714,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),sK0) = iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(equality_resolution,[status(thm)],[c_537]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_2,plain,
% 1.15/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.15/1.06      | ~ v1_relat_1(X1)
% 1.15/1.06      | v1_relat_1(X0) ),
% 1.15/1.06      inference(cnf_transformation,[],[f27]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_209,plain,
% 1.15/1.06      ( ~ v1_relat_1(X0)
% 1.15/1.06      | v1_relat_1(X1)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0)
% 1.15/1.06      | sK4 != X1 ),
% 1.15/1.06      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_210,plain,
% 1.15/1.06      ( ~ v1_relat_1(X0)
% 1.15/1.06      | v1_relat_1(sK4)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0) ),
% 1.15/1.06      inference(unflattening,[status(thm)],[c_209]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_540,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0)
% 1.15/1.06      | v1_relat_1(X0) != iProver_top
% 1.15/1.06      | v1_relat_1(sK4) = iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_646,plain,
% 1.15/1.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 1.15/1.06      | v1_relat_1(sK4) = iProver_top ),
% 1.15/1.06      inference(equality_resolution,[status(thm)],[c_540]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_7,plain,
% 1.15/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.15/1.06      inference(cnf_transformation,[],[f32]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_748,plain,
% 1.15/1.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 1.15/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_749,plain,
% 1.15/1.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1010,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),sK0) = iProver_top ),
% 1.15/1.06      inference(global_propositional_subsumption,
% 1.15/1.06                [status(thm)],
% 1.15/1.06                [c_714,c_646,c_749]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1,plain,
% 1.15/1.06      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.15/1.06      inference(cnf_transformation,[],[f26]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_544,plain,
% 1.15/1.06      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1015,plain,
% 1.15/1.06      ( k2_xboole_0(k1_relat_1(sK4),sK0) = sK0 ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1010,c_544]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_0,plain,
% 1.15/1.06      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 1.15/1.06      inference(cnf_transformation,[],[f25]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_545,plain,
% 1.15/1.06      ( r1_tarski(X0,X1) = iProver_top
% 1.15/1.06      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1207,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.15/1.06      | r1_tarski(sK0,X0) != iProver_top ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1015,c_545]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_8,plain,
% 1.15/1.06      ( v5_relat_1(X0,X1)
% 1.15/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.15/1.06      inference(cnf_transformation,[],[f34]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_6,plain,
% 1.15/1.06      ( ~ v5_relat_1(X0,X1)
% 1.15/1.06      | r1_tarski(k2_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0) ),
% 1.15/1.06      inference(cnf_transformation,[],[f30]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_186,plain,
% 1.15/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.15/1.06      | r1_tarski(k2_relat_1(X0),X2)
% 1.15/1.06      | ~ v1_relat_1(X0) ),
% 1.15/1.06      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_242,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.15/1.06      | sK4 != X0 ),
% 1.15/1.06      inference(resolution_lifted,[status(thm)],[c_186,c_14]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_243,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(sK4),X0)
% 1.15/1.06      | ~ v1_relat_1(sK4)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 1.15/1.06      inference(unflattening,[status(thm)],[c_242]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_538,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))
% 1.15/1.06      | r1_tarski(k2_relat_1(sK4),X1) = iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_720,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(equality_resolution,[status(thm)],[c_538]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1060,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 1.15/1.06      inference(global_propositional_subsumption,
% 1.15/1.06                [status(thm)],
% 1.15/1.06                [c_720,c_646,c_749]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1065,plain,
% 1.15/1.06      ( k2_xboole_0(k2_relat_1(sK4),sK2) = sK2 ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1060,c_544]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1210,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 1.15/1.06      | r1_tarski(sK2,X0) != iProver_top ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1065,c_545]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_10,plain,
% 1.15/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.15/1.06      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.15/1.06      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.15/1.06      | ~ v1_relat_1(X0) ),
% 1.15/1.06      inference(cnf_transformation,[],[f35]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_11,negated_conjecture,
% 1.15/1.06      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 1.15/1.06      inference(cnf_transformation,[],[f39]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_224,plain,
% 1.15/1.06      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.15/1.06      | ~ r1_tarski(k1_relat_1(X0),X2)
% 1.15/1.06      | ~ v1_relat_1(X0)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 1.15/1.06      | sK4 != X0 ),
% 1.15/1.06      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_225,plain,
% 1.15/1.06      ( ~ r1_tarski(k2_relat_1(sK4),X0)
% 1.15/1.06      | ~ r1_tarski(k1_relat_1(sK4),X1)
% 1.15/1.06      | ~ v1_relat_1(sK4)
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
% 1.15/1.06      inference(unflattening,[status(thm)],[c_224]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_539,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 1.15/1.06      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 1.15/1.06      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_226,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 1.15/1.06      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 1.15/1.06      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.15/1.06      | v1_relat_1(sK4) != iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_778,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.15/1.06      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 1.15/1.06      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)) ),
% 1.15/1.06      inference(global_propositional_subsumption,
% 1.15/1.06                [status(thm)],
% 1.15/1.06                [c_539,c_226,c_646,c_749]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_779,plain,
% 1.15/1.06      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))
% 1.15/1.06      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 1.15/1.06      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 1.15/1.06      inference(renaming,[status(thm)],[c_778]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_787,plain,
% 1.15/1.06      ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 1.15/1.06      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top ),
% 1.15/1.06      inference(equality_resolution,[status(thm)],[c_779]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1377,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 1.15/1.06      | r1_tarski(sK2,sK3) != iProver_top ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1210,c_787]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_12,negated_conjecture,
% 1.15/1.06      ( r1_tarski(sK2,sK3) ),
% 1.15/1.06      inference(cnf_transformation,[],[f38]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_17,plain,
% 1.15/1.06      ( r1_tarski(sK2,sK3) = iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1802,plain,
% 1.15/1.06      ( r1_tarski(k1_relat_1(sK4),sK1) != iProver_top ),
% 1.15/1.06      inference(global_propositional_subsumption,
% 1.15/1.06                [status(thm)],
% 1.15/1.06                [c_1377,c_17]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_1808,plain,
% 1.15/1.06      ( r1_tarski(sK0,sK1) != iProver_top ),
% 1.15/1.06      inference(superposition,[status(thm)],[c_1207,c_1802]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_13,negated_conjecture,
% 1.15/1.06      ( r1_tarski(sK0,sK1) ),
% 1.15/1.06      inference(cnf_transformation,[],[f37]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(c_16,plain,
% 1.15/1.06      ( r1_tarski(sK0,sK1) = iProver_top ),
% 1.15/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.15/1.06  
% 1.15/1.06  cnf(contradiction,plain,
% 1.15/1.06      ( $false ),
% 1.15/1.06      inference(minisat,[status(thm)],[c_1808,c_16]) ).
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.15/1.06  
% 1.15/1.06  ------                               Statistics
% 1.15/1.06  
% 1.15/1.06  ------ General
% 1.15/1.06  
% 1.15/1.06  abstr_ref_over_cycles:                  0
% 1.15/1.06  abstr_ref_under_cycles:                 0
% 1.15/1.06  gc_basic_clause_elim:                   0
% 1.15/1.06  forced_gc_time:                         0
% 1.15/1.06  parsing_time:                           0.008
% 1.15/1.06  unif_index_cands_time:                  0.
% 1.15/1.06  unif_index_add_time:                    0.
% 1.15/1.06  orderings_time:                         0.
% 1.15/1.06  out_proof_time:                         0.008
% 1.15/1.06  total_time:                             0.132
% 1.15/1.06  num_of_symbols:                         46
% 1.15/1.06  num_of_terms:                           1537
% 1.15/1.06  
% 1.15/1.06  ------ Preprocessing
% 1.15/1.06  
% 1.15/1.06  num_of_splits:                          0
% 1.15/1.06  num_of_split_atoms:                     0
% 1.15/1.06  num_of_reused_defs:                     0
% 1.15/1.06  num_eq_ax_congr_red:                    12
% 1.15/1.06  num_of_sem_filtered_clauses:            1
% 1.15/1.06  num_of_subtypes:                        0
% 1.15/1.06  monotx_restored_types:                  0
% 1.15/1.06  sat_num_of_epr_types:                   0
% 1.15/1.06  sat_num_of_non_cyclic_types:            0
% 1.15/1.06  sat_guarded_non_collapsed_types:        0
% 1.15/1.06  num_pure_diseq_elim:                    0
% 1.15/1.06  simp_replaced_by:                       0
% 1.15/1.06  res_preprocessed:                       62
% 1.15/1.06  prep_upred:                             0
% 1.15/1.06  prep_unflattend:                        5
% 1.15/1.06  smt_new_axioms:                         0
% 1.15/1.06  pred_elim_cands:                        2
% 1.15/1.06  pred_elim:                              3
% 1.15/1.06  pred_elim_cl:                           5
% 1.15/1.06  pred_elim_cycles:                       5
% 1.15/1.06  merged_defs:                            0
% 1.15/1.06  merged_defs_ncl:                        0
% 1.15/1.06  bin_hyper_res:                          0
% 1.15/1.06  prep_cycles:                            4
% 1.15/1.06  pred_elim_time:                         0.003
% 1.15/1.06  splitting_time:                         0.
% 1.15/1.06  sem_filter_time:                        0.
% 1.15/1.06  monotx_time:                            0.
% 1.15/1.06  subtype_inf_time:                       0.
% 1.15/1.06  
% 1.15/1.06  ------ Problem properties
% 1.15/1.06  
% 1.15/1.06  clauses:                                10
% 1.15/1.06  conjectures:                            2
% 1.15/1.06  epr:                                    2
% 1.15/1.06  horn:                                   10
% 1.15/1.06  ground:                                 3
% 1.15/1.06  unary:                                  4
% 1.15/1.06  binary:                                 2
% 1.15/1.06  lits:                                   21
% 1.15/1.06  lits_eq:                                6
% 1.15/1.06  fd_pure:                                0
% 1.15/1.06  fd_pseudo:                              0
% 1.15/1.06  fd_cond:                                0
% 1.15/1.06  fd_pseudo_cond:                         0
% 1.15/1.06  ac_symbols:                             0
% 1.15/1.06  
% 1.15/1.06  ------ Propositional Solver
% 1.15/1.06  
% 1.15/1.06  prop_solver_calls:                      28
% 1.15/1.06  prop_fast_solver_calls:                 357
% 1.15/1.06  smt_solver_calls:                       0
% 1.15/1.06  smt_fast_solver_calls:                  0
% 1.15/1.06  prop_num_of_clauses:                    678
% 1.15/1.06  prop_preprocess_simplified:             2521
% 1.15/1.06  prop_fo_subsumed:                       5
% 1.15/1.06  prop_solver_time:                       0.
% 1.15/1.06  smt_solver_time:                        0.
% 1.15/1.06  smt_fast_solver_time:                   0.
% 1.15/1.06  prop_fast_solver_time:                  0.
% 1.15/1.06  prop_unsat_core_time:                   0.
% 1.15/1.06  
% 1.15/1.06  ------ QBF
% 1.15/1.06  
% 1.15/1.06  qbf_q_res:                              0
% 1.15/1.06  qbf_num_tautologies:                    0
% 1.15/1.06  qbf_prep_cycles:                        0
% 1.15/1.06  
% 1.15/1.06  ------ BMC1
% 1.15/1.06  
% 1.15/1.06  bmc1_current_bound:                     -1
% 1.15/1.06  bmc1_last_solved_bound:                 -1
% 1.15/1.06  bmc1_unsat_core_size:                   -1
% 1.15/1.06  bmc1_unsat_core_parents_size:           -1
% 1.15/1.06  bmc1_merge_next_fun:                    0
% 1.15/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.15/1.06  
% 1.15/1.06  ------ Instantiation
% 1.15/1.06  
% 1.15/1.06  inst_num_of_clauses:                    245
% 1.15/1.06  inst_num_in_passive:                    20
% 1.15/1.06  inst_num_in_active:                     148
% 1.15/1.06  inst_num_in_unprocessed:                77
% 1.15/1.06  inst_num_of_loops:                      160
% 1.15/1.06  inst_num_of_learning_restarts:          0
% 1.15/1.06  inst_num_moves_active_passive:          9
% 1.15/1.06  inst_lit_activity:                      0
% 1.15/1.06  inst_lit_activity_moves:                0
% 1.15/1.06  inst_num_tautologies:                   0
% 1.15/1.06  inst_num_prop_implied:                  0
% 1.15/1.06  inst_num_existing_simplified:           0
% 1.15/1.06  inst_num_eq_res_simplified:             0
% 1.15/1.06  inst_num_child_elim:                    0
% 1.15/1.06  inst_num_of_dismatching_blockings:      61
% 1.15/1.06  inst_num_of_non_proper_insts:           246
% 1.15/1.06  inst_num_of_duplicates:                 0
% 1.15/1.06  inst_inst_num_from_inst_to_res:         0
% 1.15/1.06  inst_dismatching_checking_time:         0.
% 1.15/1.06  
% 1.15/1.06  ------ Resolution
% 1.15/1.06  
% 1.15/1.06  res_num_of_clauses:                     0
% 1.15/1.06  res_num_in_passive:                     0
% 1.15/1.06  res_num_in_active:                      0
% 1.15/1.06  res_num_of_loops:                       66
% 1.15/1.06  res_forward_subset_subsumed:            23
% 1.15/1.06  res_backward_subset_subsumed:           0
% 1.15/1.06  res_forward_subsumed:                   0
% 1.15/1.06  res_backward_subsumed:                  0
% 1.15/1.06  res_forward_subsumption_resolution:     0
% 1.15/1.06  res_backward_subsumption_resolution:    0
% 1.15/1.06  res_clause_to_clause_subsumption:       33
% 1.15/1.06  res_orphan_elimination:                 0
% 1.15/1.06  res_tautology_del:                      32
% 1.15/1.06  res_num_eq_res_simplified:              1
% 1.15/1.06  res_num_sel_changes:                    0
% 1.15/1.06  res_moves_from_active_to_pass:          0
% 1.15/1.06  
% 1.15/1.06  ------ Superposition
% 1.15/1.06  
% 1.15/1.06  sup_time_total:                         0.
% 1.15/1.06  sup_time_generating:                    0.
% 1.15/1.06  sup_time_sim_full:                      0.
% 1.15/1.06  sup_time_sim_immed:                     0.
% 1.15/1.06  
% 1.15/1.06  sup_num_of_clauses:                     33
% 1.15/1.06  sup_num_in_active:                      31
% 1.15/1.06  sup_num_in_passive:                     2
% 1.15/1.06  sup_num_of_loops:                       30
% 1.15/1.06  sup_fw_superposition:                   6
% 1.15/1.06  sup_bw_superposition:                   14
% 1.15/1.06  sup_immediate_simplified:               0
% 1.15/1.06  sup_given_eliminated:                   0
% 1.15/1.06  comparisons_done:                       0
% 1.15/1.06  comparisons_avoided:                    0
% 1.15/1.06  
% 1.15/1.06  ------ Simplifications
% 1.15/1.06  
% 1.15/1.06  
% 1.15/1.06  sim_fw_subset_subsumed:                 0
% 1.15/1.06  sim_bw_subset_subsumed:                 1
% 1.15/1.06  sim_fw_subsumed:                        0
% 1.15/1.06  sim_bw_subsumed:                        0
% 1.15/1.06  sim_fw_subsumption_res:                 0
% 1.15/1.06  sim_bw_subsumption_res:                 0
% 1.15/1.06  sim_tautology_del:                      0
% 1.15/1.06  sim_eq_tautology_del:                   0
% 1.15/1.06  sim_eq_res_simp:                        0
% 1.15/1.06  sim_fw_demodulated:                     0
% 1.15/1.06  sim_bw_demodulated:                     0
% 1.15/1.06  sim_light_normalised:                   0
% 1.15/1.06  sim_joinable_taut:                      0
% 1.15/1.06  sim_joinable_simp:                      0
% 1.15/1.06  sim_ac_normalised:                      0
% 1.15/1.06  sim_smt_subsumption:                    0
% 1.15/1.06  
%------------------------------------------------------------------------------
