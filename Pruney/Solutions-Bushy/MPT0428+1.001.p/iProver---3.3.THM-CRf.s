%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0428+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:16 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 144 expanded)
%              Number of clauses        :   44 (  57 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 ( 446 expanded)
%              Number of equality atoms :   82 ( 181 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( k5_setfam_1(sK0,sK1) != sK0
        | ~ m1_setfam_1(sK1,sK0) )
      & ( k5_setfam_1(sK0,sK1) = sK0
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( k5_setfam_1(sK0,sK1) != sK0
      | ~ m1_setfam_1(sK1,sK0) )
    & ( k5_setfam_1(sK0,sK1) = sK0
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,
    ( k5_setfam_1(sK0,sK1) != sK0
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,
    ( k5_setfam_1(sK0,sK1) = sK0
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_558,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_561,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_830,plain,
    ( k5_setfam_1(sK0,sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_558,c_561])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_562,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1041,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_562])).

cnf(c_3,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_95,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_9,negated_conjecture,
    ( ~ m1_setfam_1(sK1,sK0)
    | k5_setfam_1(sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_103,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | k5_setfam_1(sK0,sK1) != sK0 ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,k3_tarski(X1))
    | k5_setfam_1(sK0,sK1) != sK0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_95,c_103])).

cnf(c_176,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | k5_setfam_1(sK0,sK1) != sK0 ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_238,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | k5_setfam_1(sK0,sK1) != sK0 ),
    inference(prop_impl,[status(thm)],[c_176])).

cnf(c_557,plain,
    ( k5_setfam_1(sK0,sK1) != sK0
    | r1_tarski(sK0,k3_tarski(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_1030,plain,
    ( k3_tarski(sK1) != sK0
    | r1_tarski(sK0,k3_tarski(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_830,c_557])).

cnf(c_4,plain,
    ( ~ m1_setfam_1(X0,X1)
    | r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_97,plain,
    ( ~ m1_setfam_1(X0,X1)
    | r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( m1_setfam_1(sK1,sK0)
    | k5_setfam_1(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_105,plain,
    ( m1_setfam_1(sK1,sK0)
    | k5_setfam_1(sK0,sK1) = sK0 ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_185,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | k5_setfam_1(sK0,sK1) = sK0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_97,c_105])).

cnf(c_186,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | k5_setfam_1(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_240,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | k5_setfam_1(sK0,sK1) = sK0 ),
    inference(prop_impl,[status(thm)],[c_186])).

cnf(c_556,plain,
    ( k5_setfam_1(sK0,sK1) = sK0
    | r1_tarski(sK0,k3_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_1029,plain,
    ( k3_tarski(sK1) = sK0
    | r1_tarski(sK0,k3_tarski(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_830,c_556])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_996,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | r1_tarski(k3_tarski(sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_997,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_tarski(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_680,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(sK1),X0)
    | k3_tarski(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_681,plain,
    ( k3_tarski(sK1) = X0
    | r1_tarski(X0,k3_tarski(sK1)) != iProver_top
    | r1_tarski(k3_tarski(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_683,plain,
    ( k3_tarski(sK1) = sK0
    | r1_tarski(k3_tarski(sK1),sK0) != iProver_top
    | r1_tarski(sK0,k3_tarski(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_638,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k3_tarski(sK1))
    | k3_tarski(sK1) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_639,plain,
    ( k3_tarski(sK1) != X0
    | sK0 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK0,k3_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_641,plain,
    ( k3_tarski(sK1) != sK0
    | sK0 != sK0
    | r1_tarski(sK0,k3_tarski(sK1)) = iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_38,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_33,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_35,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_34,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1041,c_1030,c_1029,c_997,c_683,c_641,c_38,c_35,c_34,c_12])).


%------------------------------------------------------------------------------
