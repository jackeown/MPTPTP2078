%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:03 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 632 expanded)
%              Number of clauses        :   77 ( 276 expanded)
%              Number of leaves         :   16 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  257 (1632 expanded)
%              Number of equality atoms :  160 ( 772 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK0) != sK1
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( k2_subset_1(sK0) = sK1
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_598,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_595,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_607,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1251,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_595,c_607])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1417,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_599])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_19])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_608,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2720,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1))) = k3_subset_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_608])).

cnf(c_59230,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,k1_xboole_0),k4_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_2720])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_605,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1653,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_605])).

cnf(c_1967,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1653,c_19])).

cnf(c_1972,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1967,c_607])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_603,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1245,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_595,c_603])).

cnf(c_1324,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1245,c_1245,c_1251])).

cnf(c_1977,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1972,c_1324])).

cnf(c_1250,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_598,c_607])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_609,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_939,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_609,c_608])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_610,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_917,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_609,c_610])).

cnf(c_3040,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_939,c_917])).

cnf(c_3149,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1250,c_1250,c_3040])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k2_subset_1(sK0) = sK1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_596,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_612,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_596,c_5])).

cnf(c_1410,plain,
    ( sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1251,c_612])).

cnf(c_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_57,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_59,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_228,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_246,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_606,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_606,c_5])).

cnf(c_631,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_229,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_657,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_694,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_695,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_732,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_933,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_1238,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != k3_subset_1(X0,X1)
    | sK1 != X2 ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1239,plain,
    ( k3_subset_1(sK0,sK1) != k3_subset_1(X0,X1)
    | sK1 != X2
    | r1_tarski(k3_subset_1(X0,X1),X2) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_1241,plain,
    ( k3_subset_1(sK0,sK1) != k3_subset_1(sK1,sK1)
    | sK1 != sK1
    | r1_tarski(k3_subset_1(sK1,sK1),sK1) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_600,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_600])).

cnf(c_1330,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_234,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_2645,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_2646,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK1,sK1)
    | sK1 != sK1
    | sK0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2645])).

cnf(c_3153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3149,c_599])).

cnf(c_3162,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k3_subset_1(sK1,sK1),sK1) = iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3153])).

cnf(c_4690,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_19,c_24,c_59,c_246,c_631,c_695,c_732,c_1241,c_1330,c_1653,c_2646,c_3162])).

cnf(c_4695,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4690,c_610])).

cnf(c_59245,plain,
    ( sK1 = sK0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_59230,c_1977,c_3149,c_4695])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k2_subset_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_597,plain,
    ( k2_subset_1(sK0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_613,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_597,c_5])).

cnf(c_1411,plain,
    ( sK1 != sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1251,c_613])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59245,c_4690,c_1411,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.95/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/2.51  
% 15.95/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.95/2.51  
% 15.95/2.51  ------  iProver source info
% 15.95/2.51  
% 15.95/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.95/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.95/2.51  git: non_committed_changes: false
% 15.95/2.51  git: last_make_outside_of_git: false
% 15.95/2.51  
% 15.95/2.51  ------ 
% 15.95/2.51  
% 15.95/2.51  ------ Input Options
% 15.95/2.51  
% 15.95/2.51  --out_options                           all
% 15.95/2.51  --tptp_safe_out                         true
% 15.95/2.51  --problem_path                          ""
% 15.95/2.51  --include_path                          ""
% 15.95/2.51  --clausifier                            res/vclausify_rel
% 15.95/2.51  --clausifier_options                    ""
% 15.95/2.51  --stdin                                 false
% 15.95/2.51  --stats_out                             all
% 15.95/2.51  
% 15.95/2.51  ------ General Options
% 15.95/2.51  
% 15.95/2.51  --fof                                   false
% 15.95/2.51  --time_out_real                         305.
% 15.95/2.51  --time_out_virtual                      -1.
% 15.95/2.51  --symbol_type_check                     false
% 15.95/2.51  --clausify_out                          false
% 15.95/2.51  --sig_cnt_out                           false
% 15.95/2.52  --trig_cnt_out                          false
% 15.95/2.52  --trig_cnt_out_tolerance                1.
% 15.95/2.52  --trig_cnt_out_sk_spl                   false
% 15.95/2.52  --abstr_cl_out                          false
% 15.95/2.52  
% 15.95/2.52  ------ Global Options
% 15.95/2.52  
% 15.95/2.52  --schedule                              default
% 15.95/2.52  --add_important_lit                     false
% 15.95/2.52  --prop_solver_per_cl                    1000
% 15.95/2.52  --min_unsat_core                        false
% 15.95/2.52  --soft_assumptions                      false
% 15.95/2.52  --soft_lemma_size                       3
% 15.95/2.52  --prop_impl_unit_size                   0
% 15.95/2.52  --prop_impl_unit                        []
% 15.95/2.52  --share_sel_clauses                     true
% 15.95/2.52  --reset_solvers                         false
% 15.95/2.52  --bc_imp_inh                            [conj_cone]
% 15.95/2.52  --conj_cone_tolerance                   3.
% 15.95/2.52  --extra_neg_conj                        none
% 15.95/2.52  --large_theory_mode                     true
% 15.95/2.52  --prolific_symb_bound                   200
% 15.95/2.52  --lt_threshold                          2000
% 15.95/2.52  --clause_weak_htbl                      true
% 15.95/2.52  --gc_record_bc_elim                     false
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing Options
% 15.95/2.52  
% 15.95/2.52  --preprocessing_flag                    true
% 15.95/2.52  --time_out_prep_mult                    0.1
% 15.95/2.52  --splitting_mode                        input
% 15.95/2.52  --splitting_grd                         true
% 15.95/2.52  --splitting_cvd                         false
% 15.95/2.52  --splitting_cvd_svl                     false
% 15.95/2.52  --splitting_nvd                         32
% 15.95/2.52  --sub_typing                            true
% 15.95/2.52  --prep_gs_sim                           true
% 15.95/2.52  --prep_unflatten                        true
% 15.95/2.52  --prep_res_sim                          true
% 15.95/2.52  --prep_upred                            true
% 15.95/2.52  --prep_sem_filter                       exhaustive
% 15.95/2.52  --prep_sem_filter_out                   false
% 15.95/2.52  --pred_elim                             true
% 15.95/2.52  --res_sim_input                         true
% 15.95/2.52  --eq_ax_congr_red                       true
% 15.95/2.52  --pure_diseq_elim                       true
% 15.95/2.52  --brand_transform                       false
% 15.95/2.52  --non_eq_to_eq                          false
% 15.95/2.52  --prep_def_merge                        true
% 15.95/2.52  --prep_def_merge_prop_impl              false
% 15.95/2.52  --prep_def_merge_mbd                    true
% 15.95/2.52  --prep_def_merge_tr_red                 false
% 15.95/2.52  --prep_def_merge_tr_cl                  false
% 15.95/2.52  --smt_preprocessing                     true
% 15.95/2.52  --smt_ac_axioms                         fast
% 15.95/2.52  --preprocessed_out                      false
% 15.95/2.52  --preprocessed_stats                    false
% 15.95/2.52  
% 15.95/2.52  ------ Abstraction refinement Options
% 15.95/2.52  
% 15.95/2.52  --abstr_ref                             []
% 15.95/2.52  --abstr_ref_prep                        false
% 15.95/2.52  --abstr_ref_until_sat                   false
% 15.95/2.52  --abstr_ref_sig_restrict                funpre
% 15.95/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.95/2.52  --abstr_ref_under                       []
% 15.95/2.52  
% 15.95/2.52  ------ SAT Options
% 15.95/2.52  
% 15.95/2.52  --sat_mode                              false
% 15.95/2.52  --sat_fm_restart_options                ""
% 15.95/2.52  --sat_gr_def                            false
% 15.95/2.52  --sat_epr_types                         true
% 15.95/2.52  --sat_non_cyclic_types                  false
% 15.95/2.52  --sat_finite_models                     false
% 15.95/2.52  --sat_fm_lemmas                         false
% 15.95/2.52  --sat_fm_prep                           false
% 15.95/2.52  --sat_fm_uc_incr                        true
% 15.95/2.52  --sat_out_model                         small
% 15.95/2.52  --sat_out_clauses                       false
% 15.95/2.52  
% 15.95/2.52  ------ QBF Options
% 15.95/2.52  
% 15.95/2.52  --qbf_mode                              false
% 15.95/2.52  --qbf_elim_univ                         false
% 15.95/2.52  --qbf_dom_inst                          none
% 15.95/2.52  --qbf_dom_pre_inst                      false
% 15.95/2.52  --qbf_sk_in                             false
% 15.95/2.52  --qbf_pred_elim                         true
% 15.95/2.52  --qbf_split                             512
% 15.95/2.52  
% 15.95/2.52  ------ BMC1 Options
% 15.95/2.52  
% 15.95/2.52  --bmc1_incremental                      false
% 15.95/2.52  --bmc1_axioms                           reachable_all
% 15.95/2.52  --bmc1_min_bound                        0
% 15.95/2.52  --bmc1_max_bound                        -1
% 15.95/2.52  --bmc1_max_bound_default                -1
% 15.95/2.52  --bmc1_symbol_reachability              true
% 15.95/2.52  --bmc1_property_lemmas                  false
% 15.95/2.52  --bmc1_k_induction                      false
% 15.95/2.52  --bmc1_non_equiv_states                 false
% 15.95/2.52  --bmc1_deadlock                         false
% 15.95/2.52  --bmc1_ucm                              false
% 15.95/2.52  --bmc1_add_unsat_core                   none
% 15.95/2.52  --bmc1_unsat_core_children              false
% 15.95/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.95/2.52  --bmc1_out_stat                         full
% 15.95/2.52  --bmc1_ground_init                      false
% 15.95/2.52  --bmc1_pre_inst_next_state              false
% 15.95/2.52  --bmc1_pre_inst_state                   false
% 15.95/2.52  --bmc1_pre_inst_reach_state             false
% 15.95/2.52  --bmc1_out_unsat_core                   false
% 15.95/2.52  --bmc1_aig_witness_out                  false
% 15.95/2.52  --bmc1_verbose                          false
% 15.95/2.52  --bmc1_dump_clauses_tptp                false
% 15.95/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.95/2.52  --bmc1_dump_file                        -
% 15.95/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.95/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.95/2.52  --bmc1_ucm_extend_mode                  1
% 15.95/2.52  --bmc1_ucm_init_mode                    2
% 15.95/2.52  --bmc1_ucm_cone_mode                    none
% 15.95/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.95/2.52  --bmc1_ucm_relax_model                  4
% 15.95/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.95/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.95/2.52  --bmc1_ucm_layered_model                none
% 15.95/2.52  --bmc1_ucm_max_lemma_size               10
% 15.95/2.52  
% 15.95/2.52  ------ AIG Options
% 15.95/2.52  
% 15.95/2.52  --aig_mode                              false
% 15.95/2.52  
% 15.95/2.52  ------ Instantiation Options
% 15.95/2.52  
% 15.95/2.52  --instantiation_flag                    true
% 15.95/2.52  --inst_sos_flag                         true
% 15.95/2.52  --inst_sos_phase                        true
% 15.95/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.95/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.95/2.52  --inst_lit_sel_side                     num_symb
% 15.95/2.52  --inst_solver_per_active                1400
% 15.95/2.52  --inst_solver_calls_frac                1.
% 15.95/2.52  --inst_passive_queue_type               priority_queues
% 15.95/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.95/2.52  --inst_passive_queues_freq              [25;2]
% 15.95/2.52  --inst_dismatching                      true
% 15.95/2.52  --inst_eager_unprocessed_to_passive     true
% 15.95/2.52  --inst_prop_sim_given                   true
% 15.95/2.52  --inst_prop_sim_new                     false
% 15.95/2.52  --inst_subs_new                         false
% 15.95/2.52  --inst_eq_res_simp                      false
% 15.95/2.52  --inst_subs_given                       false
% 15.95/2.52  --inst_orphan_elimination               true
% 15.95/2.52  --inst_learning_loop_flag               true
% 15.95/2.52  --inst_learning_start                   3000
% 15.95/2.52  --inst_learning_factor                  2
% 15.95/2.52  --inst_start_prop_sim_after_learn       3
% 15.95/2.52  --inst_sel_renew                        solver
% 15.95/2.52  --inst_lit_activity_flag                true
% 15.95/2.52  --inst_restr_to_given                   false
% 15.95/2.52  --inst_activity_threshold               500
% 15.95/2.52  --inst_out_proof                        true
% 15.95/2.52  
% 15.95/2.52  ------ Resolution Options
% 15.95/2.52  
% 15.95/2.52  --resolution_flag                       true
% 15.95/2.52  --res_lit_sel                           adaptive
% 15.95/2.52  --res_lit_sel_side                      none
% 15.95/2.52  --res_ordering                          kbo
% 15.95/2.52  --res_to_prop_solver                    active
% 15.95/2.52  --res_prop_simpl_new                    false
% 15.95/2.52  --res_prop_simpl_given                  true
% 15.95/2.52  --res_passive_queue_type                priority_queues
% 15.95/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.95/2.52  --res_passive_queues_freq               [15;5]
% 15.95/2.52  --res_forward_subs                      full
% 15.95/2.52  --res_backward_subs                     full
% 15.95/2.52  --res_forward_subs_resolution           true
% 15.95/2.52  --res_backward_subs_resolution          true
% 15.95/2.52  --res_orphan_elimination                true
% 15.95/2.52  --res_time_limit                        2.
% 15.95/2.52  --res_out_proof                         true
% 15.95/2.52  
% 15.95/2.52  ------ Superposition Options
% 15.95/2.52  
% 15.95/2.52  --superposition_flag                    true
% 15.95/2.52  --sup_passive_queue_type                priority_queues
% 15.95/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.95/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.95/2.52  --demod_completeness_check              fast
% 15.95/2.52  --demod_use_ground                      true
% 15.95/2.52  --sup_to_prop_solver                    passive
% 15.95/2.52  --sup_prop_simpl_new                    true
% 15.95/2.52  --sup_prop_simpl_given                  true
% 15.95/2.52  --sup_fun_splitting                     true
% 15.95/2.52  --sup_smt_interval                      50000
% 15.95/2.52  
% 15.95/2.52  ------ Superposition Simplification Setup
% 15.95/2.52  
% 15.95/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.95/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.95/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.95/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.95/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.95/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.95/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.95/2.52  --sup_immed_triv                        [TrivRules]
% 15.95/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_immed_bw_main                     []
% 15.95/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.95/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.95/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_input_bw                          []
% 15.95/2.52  
% 15.95/2.52  ------ Combination Options
% 15.95/2.52  
% 15.95/2.52  --comb_res_mult                         3
% 15.95/2.52  --comb_sup_mult                         2
% 15.95/2.52  --comb_inst_mult                        10
% 15.95/2.52  
% 15.95/2.52  ------ Debug Options
% 15.95/2.52  
% 15.95/2.52  --dbg_backtrace                         false
% 15.95/2.52  --dbg_dump_prop_clauses                 false
% 15.95/2.52  --dbg_dump_prop_clauses_file            -
% 15.95/2.52  --dbg_out_stat                          false
% 15.95/2.52  ------ Parsing...
% 15.95/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.95/2.52  ------ Proving...
% 15.95/2.52  ------ Problem Properties 
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  clauses                                 19
% 15.95/2.52  conjectures                             3
% 15.95/2.52  EPR                                     1
% 15.95/2.52  Horn                                    18
% 15.95/2.52  unary                                   7
% 15.95/2.52  binary                                  8
% 15.95/2.52  lits                                    37
% 15.95/2.52  lits eq                                 11
% 15.95/2.52  fd_pure                                 0
% 15.95/2.52  fd_pseudo                               0
% 15.95/2.52  fd_cond                                 0
% 15.95/2.52  fd_pseudo_cond                          0
% 15.95/2.52  AC symbols                              0
% 15.95/2.52  
% 15.95/2.52  ------ Schedule dynamic 5 is on 
% 15.95/2.52  
% 15.95/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  ------ 
% 15.95/2.52  Current options:
% 15.95/2.52  ------ 
% 15.95/2.52  
% 15.95/2.52  ------ Input Options
% 15.95/2.52  
% 15.95/2.52  --out_options                           all
% 15.95/2.52  --tptp_safe_out                         true
% 15.95/2.52  --problem_path                          ""
% 15.95/2.52  --include_path                          ""
% 15.95/2.52  --clausifier                            res/vclausify_rel
% 15.95/2.52  --clausifier_options                    ""
% 15.95/2.52  --stdin                                 false
% 15.95/2.52  --stats_out                             all
% 15.95/2.52  
% 15.95/2.52  ------ General Options
% 15.95/2.52  
% 15.95/2.52  --fof                                   false
% 15.95/2.52  --time_out_real                         305.
% 15.95/2.52  --time_out_virtual                      -1.
% 15.95/2.52  --symbol_type_check                     false
% 15.95/2.52  --clausify_out                          false
% 15.95/2.52  --sig_cnt_out                           false
% 15.95/2.52  --trig_cnt_out                          false
% 15.95/2.52  --trig_cnt_out_tolerance                1.
% 15.95/2.52  --trig_cnt_out_sk_spl                   false
% 15.95/2.52  --abstr_cl_out                          false
% 15.95/2.52  
% 15.95/2.52  ------ Global Options
% 15.95/2.52  
% 15.95/2.52  --schedule                              default
% 15.95/2.52  --add_important_lit                     false
% 15.95/2.52  --prop_solver_per_cl                    1000
% 15.95/2.52  --min_unsat_core                        false
% 15.95/2.52  --soft_assumptions                      false
% 15.95/2.52  --soft_lemma_size                       3
% 15.95/2.52  --prop_impl_unit_size                   0
% 15.95/2.52  --prop_impl_unit                        []
% 15.95/2.52  --share_sel_clauses                     true
% 15.95/2.52  --reset_solvers                         false
% 15.95/2.52  --bc_imp_inh                            [conj_cone]
% 15.95/2.52  --conj_cone_tolerance                   3.
% 15.95/2.52  --extra_neg_conj                        none
% 15.95/2.52  --large_theory_mode                     true
% 15.95/2.52  --prolific_symb_bound                   200
% 15.95/2.52  --lt_threshold                          2000
% 15.95/2.52  --clause_weak_htbl                      true
% 15.95/2.52  --gc_record_bc_elim                     false
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing Options
% 15.95/2.52  
% 15.95/2.52  --preprocessing_flag                    true
% 15.95/2.52  --time_out_prep_mult                    0.1
% 15.95/2.52  --splitting_mode                        input
% 15.95/2.52  --splitting_grd                         true
% 15.95/2.52  --splitting_cvd                         false
% 15.95/2.52  --splitting_cvd_svl                     false
% 15.95/2.52  --splitting_nvd                         32
% 15.95/2.52  --sub_typing                            true
% 15.95/2.52  --prep_gs_sim                           true
% 15.95/2.52  --prep_unflatten                        true
% 15.95/2.52  --prep_res_sim                          true
% 15.95/2.52  --prep_upred                            true
% 15.95/2.52  --prep_sem_filter                       exhaustive
% 15.95/2.52  --prep_sem_filter_out                   false
% 15.95/2.52  --pred_elim                             true
% 15.95/2.52  --res_sim_input                         true
% 15.95/2.52  --eq_ax_congr_red                       true
% 15.95/2.52  --pure_diseq_elim                       true
% 15.95/2.52  --brand_transform                       false
% 15.95/2.52  --non_eq_to_eq                          false
% 15.95/2.52  --prep_def_merge                        true
% 15.95/2.52  --prep_def_merge_prop_impl              false
% 15.95/2.52  --prep_def_merge_mbd                    true
% 15.95/2.52  --prep_def_merge_tr_red                 false
% 15.95/2.52  --prep_def_merge_tr_cl                  false
% 15.95/2.52  --smt_preprocessing                     true
% 15.95/2.52  --smt_ac_axioms                         fast
% 15.95/2.52  --preprocessed_out                      false
% 15.95/2.52  --preprocessed_stats                    false
% 15.95/2.52  
% 15.95/2.52  ------ Abstraction refinement Options
% 15.95/2.52  
% 15.95/2.52  --abstr_ref                             []
% 15.95/2.52  --abstr_ref_prep                        false
% 15.95/2.52  --abstr_ref_until_sat                   false
% 15.95/2.52  --abstr_ref_sig_restrict                funpre
% 15.95/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.95/2.52  --abstr_ref_under                       []
% 15.95/2.52  
% 15.95/2.52  ------ SAT Options
% 15.95/2.52  
% 15.95/2.52  --sat_mode                              false
% 15.95/2.52  --sat_fm_restart_options                ""
% 15.95/2.52  --sat_gr_def                            false
% 15.95/2.52  --sat_epr_types                         true
% 15.95/2.52  --sat_non_cyclic_types                  false
% 15.95/2.52  --sat_finite_models                     false
% 15.95/2.52  --sat_fm_lemmas                         false
% 15.95/2.52  --sat_fm_prep                           false
% 15.95/2.52  --sat_fm_uc_incr                        true
% 15.95/2.52  --sat_out_model                         small
% 15.95/2.52  --sat_out_clauses                       false
% 15.95/2.52  
% 15.95/2.52  ------ QBF Options
% 15.95/2.52  
% 15.95/2.52  --qbf_mode                              false
% 15.95/2.52  --qbf_elim_univ                         false
% 15.95/2.52  --qbf_dom_inst                          none
% 15.95/2.52  --qbf_dom_pre_inst                      false
% 15.95/2.52  --qbf_sk_in                             false
% 15.95/2.52  --qbf_pred_elim                         true
% 15.95/2.52  --qbf_split                             512
% 15.95/2.52  
% 15.95/2.52  ------ BMC1 Options
% 15.95/2.52  
% 15.95/2.52  --bmc1_incremental                      false
% 15.95/2.52  --bmc1_axioms                           reachable_all
% 15.95/2.52  --bmc1_min_bound                        0
% 15.95/2.52  --bmc1_max_bound                        -1
% 15.95/2.52  --bmc1_max_bound_default                -1
% 15.95/2.52  --bmc1_symbol_reachability              true
% 15.95/2.52  --bmc1_property_lemmas                  false
% 15.95/2.52  --bmc1_k_induction                      false
% 15.95/2.52  --bmc1_non_equiv_states                 false
% 15.95/2.52  --bmc1_deadlock                         false
% 15.95/2.52  --bmc1_ucm                              false
% 15.95/2.52  --bmc1_add_unsat_core                   none
% 15.95/2.52  --bmc1_unsat_core_children              false
% 15.95/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.95/2.52  --bmc1_out_stat                         full
% 15.95/2.52  --bmc1_ground_init                      false
% 15.95/2.52  --bmc1_pre_inst_next_state              false
% 15.95/2.52  --bmc1_pre_inst_state                   false
% 15.95/2.52  --bmc1_pre_inst_reach_state             false
% 15.95/2.52  --bmc1_out_unsat_core                   false
% 15.95/2.52  --bmc1_aig_witness_out                  false
% 15.95/2.52  --bmc1_verbose                          false
% 15.95/2.52  --bmc1_dump_clauses_tptp                false
% 15.95/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.95/2.52  --bmc1_dump_file                        -
% 15.95/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.95/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.95/2.52  --bmc1_ucm_extend_mode                  1
% 15.95/2.52  --bmc1_ucm_init_mode                    2
% 15.95/2.52  --bmc1_ucm_cone_mode                    none
% 15.95/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.95/2.52  --bmc1_ucm_relax_model                  4
% 15.95/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.95/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.95/2.52  --bmc1_ucm_layered_model                none
% 15.95/2.52  --bmc1_ucm_max_lemma_size               10
% 15.95/2.52  
% 15.95/2.52  ------ AIG Options
% 15.95/2.52  
% 15.95/2.52  --aig_mode                              false
% 15.95/2.52  
% 15.95/2.52  ------ Instantiation Options
% 15.95/2.52  
% 15.95/2.52  --instantiation_flag                    true
% 15.95/2.52  --inst_sos_flag                         true
% 15.95/2.52  --inst_sos_phase                        true
% 15.95/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.95/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.95/2.52  --inst_lit_sel_side                     none
% 15.95/2.52  --inst_solver_per_active                1400
% 15.95/2.52  --inst_solver_calls_frac                1.
% 15.95/2.52  --inst_passive_queue_type               priority_queues
% 15.95/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.95/2.52  --inst_passive_queues_freq              [25;2]
% 15.95/2.52  --inst_dismatching                      true
% 15.95/2.52  --inst_eager_unprocessed_to_passive     true
% 15.95/2.52  --inst_prop_sim_given                   true
% 15.95/2.52  --inst_prop_sim_new                     false
% 15.95/2.52  --inst_subs_new                         false
% 15.95/2.52  --inst_eq_res_simp                      false
% 15.95/2.52  --inst_subs_given                       false
% 15.95/2.52  --inst_orphan_elimination               true
% 15.95/2.52  --inst_learning_loop_flag               true
% 15.95/2.52  --inst_learning_start                   3000
% 15.95/2.52  --inst_learning_factor                  2
% 15.95/2.52  --inst_start_prop_sim_after_learn       3
% 15.95/2.52  --inst_sel_renew                        solver
% 15.95/2.52  --inst_lit_activity_flag                true
% 15.95/2.52  --inst_restr_to_given                   false
% 15.95/2.52  --inst_activity_threshold               500
% 15.95/2.52  --inst_out_proof                        true
% 15.95/2.52  
% 15.95/2.52  ------ Resolution Options
% 15.95/2.52  
% 15.95/2.52  --resolution_flag                       false
% 15.95/2.52  --res_lit_sel                           adaptive
% 15.95/2.52  --res_lit_sel_side                      none
% 15.95/2.52  --res_ordering                          kbo
% 15.95/2.52  --res_to_prop_solver                    active
% 15.95/2.52  --res_prop_simpl_new                    false
% 15.95/2.52  --res_prop_simpl_given                  true
% 15.95/2.52  --res_passive_queue_type                priority_queues
% 15.95/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.95/2.52  --res_passive_queues_freq               [15;5]
% 15.95/2.52  --res_forward_subs                      full
% 15.95/2.52  --res_backward_subs                     full
% 15.95/2.52  --res_forward_subs_resolution           true
% 15.95/2.52  --res_backward_subs_resolution          true
% 15.95/2.52  --res_orphan_elimination                true
% 15.95/2.52  --res_time_limit                        2.
% 15.95/2.52  --res_out_proof                         true
% 15.95/2.52  
% 15.95/2.52  ------ Superposition Options
% 15.95/2.52  
% 15.95/2.52  --superposition_flag                    true
% 15.95/2.52  --sup_passive_queue_type                priority_queues
% 15.95/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.95/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.95/2.52  --demod_completeness_check              fast
% 15.95/2.52  --demod_use_ground                      true
% 15.95/2.52  --sup_to_prop_solver                    passive
% 15.95/2.52  --sup_prop_simpl_new                    true
% 15.95/2.52  --sup_prop_simpl_given                  true
% 15.95/2.52  --sup_fun_splitting                     true
% 15.95/2.52  --sup_smt_interval                      50000
% 15.95/2.52  
% 15.95/2.52  ------ Superposition Simplification Setup
% 15.95/2.52  
% 15.95/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.95/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.95/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.95/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.95/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.95/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.95/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.95/2.52  --sup_immed_triv                        [TrivRules]
% 15.95/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_immed_bw_main                     []
% 15.95/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.95/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.95/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.52  --sup_input_bw                          []
% 15.95/2.52  
% 15.95/2.52  ------ Combination Options
% 15.95/2.52  
% 15.95/2.52  --comb_res_mult                         3
% 15.95/2.52  --comb_sup_mult                         2
% 15.95/2.52  --comb_inst_mult                        10
% 15.95/2.52  
% 15.95/2.52  ------ Debug Options
% 15.95/2.52  
% 15.95/2.52  --dbg_backtrace                         false
% 15.95/2.52  --dbg_dump_prop_clauses                 false
% 15.95/2.52  --dbg_dump_prop_clauses_file            -
% 15.95/2.52  --dbg_out_stat                          false
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  ------ Proving...
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  % SZS status Theorem for theBenchmark.p
% 15.95/2.52  
% 15.95/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.95/2.52  
% 15.95/2.52  fof(f15,axiom,(
% 15.95/2.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f50,plain,(
% 15.95/2.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f15])).
% 15.95/2.52  
% 15.95/2.52  fof(f16,conjecture,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f17,negated_conjecture,(
% 15.95/2.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 15.95/2.52    inference(negated_conjecture,[],[f16])).
% 15.95/2.52  
% 15.95/2.52  fof(f29,plain,(
% 15.95/2.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(ennf_transformation,[],[f17])).
% 15.95/2.52  
% 15.95/2.52  fof(f31,plain,(
% 15.95/2.52    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(nnf_transformation,[],[f29])).
% 15.95/2.52  
% 15.95/2.52  fof(f32,plain,(
% 15.95/2.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(flattening,[],[f31])).
% 15.95/2.52  
% 15.95/2.52  fof(f33,plain,(
% 15.95/2.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 15.95/2.52    introduced(choice_axiom,[])).
% 15.95/2.52  
% 15.95/2.52  fof(f34,plain,(
% 15.95/2.52    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 15.95/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 15.95/2.52  
% 15.95/2.52  fof(f51,plain,(
% 15.95/2.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 15.95/2.52    inference(cnf_transformation,[],[f34])).
% 15.95/2.52  
% 15.95/2.52  fof(f7,axiom,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f20,plain,(
% 15.95/2.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(ennf_transformation,[],[f7])).
% 15.95/2.52  
% 15.95/2.52  fof(f41,plain,(
% 15.95/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f20])).
% 15.95/2.52  
% 15.95/2.52  fof(f14,axiom,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f28,plain,(
% 15.95/2.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(ennf_transformation,[],[f14])).
% 15.95/2.52  
% 15.95/2.52  fof(f30,plain,(
% 15.95/2.52    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(nnf_transformation,[],[f28])).
% 15.95/2.52  
% 15.95/2.52  fof(f48,plain,(
% 15.95/2.52    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f30])).
% 15.95/2.52  
% 15.95/2.52  fof(f4,axiom,(
% 15.95/2.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f19,plain,(
% 15.95/2.52    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 15.95/2.52    inference(ennf_transformation,[],[f4])).
% 15.95/2.52  
% 15.95/2.52  fof(f38,plain,(
% 15.95/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 15.95/2.52    inference(cnf_transformation,[],[f19])).
% 15.95/2.52  
% 15.95/2.52  fof(f9,axiom,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f21,plain,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(ennf_transformation,[],[f9])).
% 15.95/2.52  
% 15.95/2.52  fof(f43,plain,(
% 15.95/2.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f21])).
% 15.95/2.52  
% 15.95/2.52  fof(f11,axiom,(
% 15.95/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f24,plain,(
% 15.95/2.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.95/2.52    inference(ennf_transformation,[],[f11])).
% 15.95/2.52  
% 15.95/2.52  fof(f45,plain,(
% 15.95/2.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f24])).
% 15.95/2.52  
% 15.95/2.52  fof(f3,axiom,(
% 15.95/2.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f37,plain,(
% 15.95/2.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.95/2.52    inference(cnf_transformation,[],[f3])).
% 15.95/2.52  
% 15.95/2.52  fof(f2,axiom,(
% 15.95/2.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f18,plain,(
% 15.95/2.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.95/2.52    inference(ennf_transformation,[],[f2])).
% 15.95/2.52  
% 15.95/2.52  fof(f36,plain,(
% 15.95/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.95/2.52    inference(cnf_transformation,[],[f18])).
% 15.95/2.52  
% 15.95/2.52  fof(f52,plain,(
% 15.95/2.52    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 15.95/2.52    inference(cnf_transformation,[],[f34])).
% 15.95/2.52  
% 15.95/2.52  fof(f6,axiom,(
% 15.95/2.52    ! [X0] : k2_subset_1(X0) = X0),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f40,plain,(
% 15.95/2.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.95/2.52    inference(cnf_transformation,[],[f6])).
% 15.95/2.52  
% 15.95/2.52  fof(f8,axiom,(
% 15.95/2.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.95/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.95/2.52  
% 15.95/2.52  fof(f42,plain,(
% 15.95/2.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f8])).
% 15.95/2.52  
% 15.95/2.52  fof(f49,plain,(
% 15.95/2.52    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.95/2.52    inference(cnf_transformation,[],[f30])).
% 15.95/2.52  
% 15.95/2.52  fof(f53,plain,(
% 15.95/2.52    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 15.95/2.52    inference(cnf_transformation,[],[f34])).
% 15.95/2.52  
% 15.95/2.52  cnf(c_15,plain,
% 15.95/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f50]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_598,plain,
% 15.95/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_18,negated_conjecture,
% 15.95/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f51]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_595,plain,
% 15.95/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_6,plain,
% 15.95/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.95/2.52      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.95/2.52      inference(cnf_transformation,[],[f41]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_607,plain,
% 15.95/2.52      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 15.95/2.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1251,plain,
% 15.95/2.52      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_595,c_607]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_14,plain,
% 15.95/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.95/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.95/2.52      | ~ r1_tarski(X0,X2)
% 15.95/2.52      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f48]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_599,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | r1_tarski(X0,X2) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1417,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | r1_tarski(X0,sK1) != iProver_top
% 15.95/2.52      | r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,X0)) = iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_1251,c_599]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_19,plain,
% 15.95/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_2714,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | r1_tarski(X0,sK1) != iProver_top
% 15.95/2.52      | r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,X0)) = iProver_top ),
% 15.95/2.52      inference(global_propositional_subsumption,
% 15.95/2.52                [status(thm)],
% 15.95/2.52                [c_1417,c_19]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_3,plain,
% 15.95/2.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 15.95/2.52      inference(cnf_transformation,[],[f38]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_608,plain,
% 15.95/2.52      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 15.95/2.52      | r1_tarski(X0,X1) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_2720,plain,
% 15.95/2.52      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1))) = k3_subset_1(sK0,X0)
% 15.95/2.52      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | r1_tarski(X0,sK1) != iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_2714,c_608]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_59230,plain,
% 15.95/2.52      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,k1_xboole_0),k4_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k1_xboole_0)
% 15.95/2.52      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_598,c_2720]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_8,plain,
% 15.95/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.95/2.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f43]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_605,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1653,plain,
% 15.95/2.52      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 15.95/2.52      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_1251,c_605]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1967,plain,
% 15.95/2.52      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 15.95/2.52      inference(global_propositional_subsumption,
% 15.95/2.52                [status(thm)],
% 15.95/2.52                [c_1653,c_19]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1972,plain,
% 15.95/2.52      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_1967,c_607]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_10,plain,
% 15.95/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.95/2.52      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.95/2.52      inference(cnf_transformation,[],[f45]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_603,plain,
% 15.95/2.52      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.95/2.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1245,plain,
% 15.95/2.52      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_595,c_603]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1324,plain,
% 15.95/2.52      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 15.95/2.52      inference(light_normalisation,[status(thm)],[c_1245,c_1245,c_1251]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1977,plain,
% 15.95/2.52      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 15.95/2.52      inference(light_normalisation,[status(thm)],[c_1972,c_1324]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1250,plain,
% 15.95/2.52      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_598,c_607]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_2,plain,
% 15.95/2.52      ( r1_tarski(k1_xboole_0,X0) ),
% 15.95/2.52      inference(cnf_transformation,[],[f37]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_609,plain,
% 15.95/2.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_939,plain,
% 15.95/2.52      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_609,c_608]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1,plain,
% 15.95/2.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.95/2.52      inference(cnf_transformation,[],[f36]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_610,plain,
% 15.95/2.52      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_917,plain,
% 15.95/2.52      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_609,c_610]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_3040,plain,
% 15.95/2.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_939,c_917]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_3149,plain,
% 15.95/2.52      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.95/2.52      inference(light_normalisation,[status(thm)],[c_1250,c_1250,c_3040]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_17,negated_conjecture,
% 15.95/2.52      ( r1_tarski(k3_subset_1(sK0,sK1),sK1) | k2_subset_1(sK0) = sK1 ),
% 15.95/2.52      inference(cnf_transformation,[],[f52]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_596,plain,
% 15.95/2.52      ( k2_subset_1(sK0) = sK1
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_5,plain,
% 15.95/2.52      ( k2_subset_1(X0) = X0 ),
% 15.95/2.52      inference(cnf_transformation,[],[f40]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_612,plain,
% 15.95/2.52      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(demodulation,[status(thm)],[c_596,c_5]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1410,plain,
% 15.95/2.52      ( sK1 = sK0 | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(demodulation,[status(thm)],[c_1251,c_612]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_22,plain,
% 15.95/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_24,plain,
% 15.95/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_22]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_57,plain,
% 15.95/2.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_59,plain,
% 15.95/2.52      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_57]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_228,plain,( X0 = X0 ),theory(equality) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_246,plain,
% 15.95/2.52      ( sK1 = sK1 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_228]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_7,plain,
% 15.95/2.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f42]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_606,plain,
% 15.95/2.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_611,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.95/2.52      inference(light_normalisation,[status(thm)],[c_606,c_5]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_631,plain,
% 15.95/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_611]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_229,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_657,plain,
% 15.95/2.52      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_229]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_694,plain,
% 15.95/2.52      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_657]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_695,plain,
% 15.95/2.52      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_694]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_732,plain,
% 15.95/2.52      ( sK0 = sK0 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_228]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_231,plain,
% 15.95/2.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.95/2.52      theory(equality) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_933,plain,
% 15.95/2.52      ( ~ r1_tarski(X0,X1)
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 15.95/2.52      | k3_subset_1(sK0,sK1) != X0
% 15.95/2.52      | sK1 != X1 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_231]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1238,plain,
% 15.95/2.52      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 15.95/2.52      | k3_subset_1(sK0,sK1) != k3_subset_1(X0,X1)
% 15.95/2.52      | sK1 != X2 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_933]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1239,plain,
% 15.95/2.52      ( k3_subset_1(sK0,sK1) != k3_subset_1(X0,X1)
% 15.95/2.52      | sK1 != X2
% 15.95/2.52      | r1_tarski(k3_subset_1(X0,X1),X2) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1241,plain,
% 15.95/2.52      ( k3_subset_1(sK0,sK1) != k3_subset_1(sK1,sK1)
% 15.95/2.52      | sK1 != sK1
% 15.95/2.52      | r1_tarski(k3_subset_1(sK1,sK1),sK1) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_1239]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_13,plain,
% 15.95/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.95/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.95/2.52      | r1_tarski(X0,X2)
% 15.95/2.52      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 15.95/2.52      inference(cnf_transformation,[],[f49]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_600,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | r1_tarski(X0,X2) = iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1325,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
% 15.95/2.52      | r1_tarski(k4_xboole_0(sK0,sK1),X0) = iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_1324,c_600]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1330,plain,
% 15.95/2.52      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top
% 15.95/2.52      | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_1325]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_234,plain,
% 15.95/2.52      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 15.95/2.52      theory(equality) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_2645,plain,
% 15.95/2.52      ( k3_subset_1(sK0,sK1) = k3_subset_1(X0,X1)
% 15.95/2.52      | sK1 != X1
% 15.95/2.52      | sK0 != X0 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_234]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_2646,plain,
% 15.95/2.52      ( k3_subset_1(sK0,sK1) = k3_subset_1(sK1,sK1)
% 15.95/2.52      | sK1 != sK1
% 15.95/2.52      | sK0 != sK1 ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_2645]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_3153,plain,
% 15.95/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 15.95/2.52      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_3149,c_599]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_3162,plain,
% 15.95/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
% 15.95/2.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top
% 15.95/2.52      | r1_tarski(k3_subset_1(sK1,sK1),sK1) = iProver_top
% 15.95/2.52      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 15.95/2.52      inference(instantiation,[status(thm)],[c_3153]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_4690,plain,
% 15.95/2.52      ( r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
% 15.95/2.52      inference(global_propositional_subsumption,
% 15.95/2.52                [status(thm)],
% 15.95/2.52                [c_1410,c_19,c_24,c_59,c_246,c_631,c_695,c_732,c_1241,
% 15.95/2.52                 c_1330,c_1653,c_2646,c_3162]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_4695,plain,
% 15.95/2.52      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) = sK1 ),
% 15.95/2.52      inference(superposition,[status(thm)],[c_4690,c_610]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_59245,plain,
% 15.95/2.52      ( sK1 = sK0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 15.95/2.52      inference(demodulation,
% 15.95/2.52                [status(thm)],
% 15.95/2.52                [c_59230,c_1977,c_3149,c_4695]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_16,negated_conjecture,
% 15.95/2.52      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) | k2_subset_1(sK0) != sK1 ),
% 15.95/2.52      inference(cnf_transformation,[],[f53]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_597,plain,
% 15.95/2.52      ( k2_subset_1(sK0) != sK1
% 15.95/2.52      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 15.95/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_613,plain,
% 15.95/2.52      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 15.95/2.52      inference(demodulation,[status(thm)],[c_597,c_5]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(c_1411,plain,
% 15.95/2.52      ( sK1 != sK0 | r1_tarski(k4_xboole_0(sK0,sK1),sK1) != iProver_top ),
% 15.95/2.52      inference(demodulation,[status(thm)],[c_1251,c_613]) ).
% 15.95/2.52  
% 15.95/2.52  cnf(contradiction,plain,
% 15.95/2.52      ( $false ),
% 15.95/2.52      inference(minisat,[status(thm)],[c_59245,c_4690,c_1411,c_59]) ).
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.95/2.52  
% 15.95/2.52  ------                               Statistics
% 15.95/2.52  
% 15.95/2.52  ------ General
% 15.95/2.52  
% 15.95/2.52  abstr_ref_over_cycles:                  0
% 15.95/2.52  abstr_ref_under_cycles:                 0
% 15.95/2.52  gc_basic_clause_elim:                   0
% 15.95/2.52  forced_gc_time:                         0
% 15.95/2.52  parsing_time:                           0.01
% 15.95/2.52  unif_index_cands_time:                  0.
% 15.95/2.52  unif_index_add_time:                    0.
% 15.95/2.52  orderings_time:                         0.
% 15.95/2.52  out_proof_time:                         0.021
% 15.95/2.52  total_time:                             1.809
% 15.95/2.52  num_of_symbols:                         42
% 15.95/2.52  num_of_terms:                           46689
% 15.95/2.52  
% 15.95/2.52  ------ Preprocessing
% 15.95/2.52  
% 15.95/2.52  num_of_splits:                          0
% 15.95/2.52  num_of_split_atoms:                     0
% 15.95/2.52  num_of_reused_defs:                     0
% 15.95/2.52  num_eq_ax_congr_red:                    8
% 15.95/2.52  num_of_sem_filtered_clauses:            1
% 15.95/2.52  num_of_subtypes:                        0
% 15.95/2.52  monotx_restored_types:                  0
% 15.95/2.52  sat_num_of_epr_types:                   0
% 15.95/2.52  sat_num_of_non_cyclic_types:            0
% 15.95/2.52  sat_guarded_non_collapsed_types:        0
% 15.95/2.52  num_pure_diseq_elim:                    0
% 15.95/2.52  simp_replaced_by:                       0
% 15.95/2.52  res_preprocessed:                       78
% 15.95/2.52  prep_upred:                             0
% 15.95/2.52  prep_unflattend:                        0
% 15.95/2.52  smt_new_axioms:                         0
% 15.95/2.52  pred_elim_cands:                        2
% 15.95/2.52  pred_elim:                              0
% 15.95/2.52  pred_elim_cl:                           0
% 15.95/2.52  pred_elim_cycles:                       1
% 15.95/2.52  merged_defs:                            6
% 15.95/2.52  merged_defs_ncl:                        0
% 15.95/2.52  bin_hyper_res:                          6
% 15.95/2.52  prep_cycles:                            3
% 15.95/2.52  pred_elim_time:                         0.
% 15.95/2.52  splitting_time:                         0.
% 15.95/2.52  sem_filter_time:                        0.
% 15.95/2.52  monotx_time:                            0.
% 15.95/2.52  subtype_inf_time:                       0.
% 15.95/2.52  
% 15.95/2.52  ------ Problem properties
% 15.95/2.52  
% 15.95/2.52  clauses:                                19
% 15.95/2.52  conjectures:                            3
% 15.95/2.52  epr:                                    1
% 15.95/2.52  horn:                                   18
% 15.95/2.52  ground:                                 3
% 15.95/2.52  unary:                                  7
% 15.95/2.52  binary:                                 8
% 15.95/2.52  lits:                                   37
% 15.95/2.52  lits_eq:                                11
% 15.95/2.52  fd_pure:                                0
% 15.95/2.52  fd_pseudo:                              0
% 15.95/2.52  fd_cond:                                0
% 15.95/2.52  fd_pseudo_cond:                         0
% 15.95/2.52  ac_symbols:                             0
% 15.95/2.52  
% 15.95/2.52  ------ Propositional Solver
% 15.95/2.52  
% 15.95/2.52  prop_solver_calls:                      34
% 15.95/2.52  prop_fast_solver_calls:                 1653
% 15.95/2.52  smt_solver_calls:                       0
% 15.95/2.52  smt_fast_solver_calls:                  0
% 15.95/2.52  prop_num_of_clauses:                    28740
% 15.95/2.52  prop_preprocess_simplified:             41242
% 15.95/2.52  prop_fo_subsumed:                       27
% 15.95/2.52  prop_solver_time:                       0.
% 15.95/2.52  smt_solver_time:                        0.
% 15.95/2.52  smt_fast_solver_time:                   0.
% 15.95/2.52  prop_fast_solver_time:                  0.
% 15.95/2.52  prop_unsat_core_time:                   0.011
% 15.95/2.52  
% 15.95/2.52  ------ QBF
% 15.95/2.52  
% 15.95/2.52  qbf_q_res:                              0
% 15.95/2.52  qbf_num_tautologies:                    0
% 15.95/2.52  qbf_prep_cycles:                        0
% 15.95/2.52  
% 15.95/2.52  ------ BMC1
% 15.95/2.52  
% 15.95/2.52  bmc1_current_bound:                     -1
% 15.95/2.52  bmc1_last_solved_bound:                 -1
% 15.95/2.52  bmc1_unsat_core_size:                   -1
% 15.95/2.52  bmc1_unsat_core_parents_size:           -1
% 15.95/2.52  bmc1_merge_next_fun:                    0
% 15.95/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.95/2.52  
% 15.95/2.52  ------ Instantiation
% 15.95/2.52  
% 15.95/2.52  inst_num_of_clauses:                    8692
% 15.95/2.52  inst_num_in_passive:                    3182
% 15.95/2.52  inst_num_in_active:                     2508
% 15.95/2.52  inst_num_in_unprocessed:                3002
% 15.95/2.52  inst_num_of_loops:                      2830
% 15.95/2.52  inst_num_of_learning_restarts:          0
% 15.95/2.52  inst_num_moves_active_passive:          316
% 15.95/2.52  inst_lit_activity:                      0
% 15.95/2.52  inst_lit_activity_moves:                1
% 15.95/2.52  inst_num_tautologies:                   0
% 15.95/2.52  inst_num_prop_implied:                  0
% 15.95/2.52  inst_num_existing_simplified:           0
% 15.95/2.52  inst_num_eq_res_simplified:             0
% 15.95/2.52  inst_num_child_elim:                    0
% 15.95/2.52  inst_num_of_dismatching_blockings:      7081
% 15.95/2.52  inst_num_of_non_proper_insts:           9807
% 15.95/2.52  inst_num_of_duplicates:                 0
% 15.95/2.52  inst_inst_num_from_inst_to_res:         0
% 15.95/2.52  inst_dismatching_checking_time:         0.
% 15.95/2.52  
% 15.95/2.52  ------ Resolution
% 15.95/2.52  
% 15.95/2.52  res_num_of_clauses:                     0
% 15.95/2.52  res_num_in_passive:                     0
% 15.95/2.52  res_num_in_active:                      0
% 15.95/2.52  res_num_of_loops:                       81
% 15.95/2.52  res_forward_subset_subsumed:            779
% 15.95/2.52  res_backward_subset_subsumed:           8
% 15.95/2.52  res_forward_subsumed:                   0
% 15.95/2.52  res_backward_subsumed:                  0
% 15.95/2.52  res_forward_subsumption_resolution:     0
% 15.95/2.52  res_backward_subsumption_resolution:    0
% 15.95/2.52  res_clause_to_clause_subsumption:       32236
% 15.95/2.52  res_orphan_elimination:                 0
% 15.95/2.52  res_tautology_del:                      522
% 15.95/2.52  res_num_eq_res_simplified:              0
% 15.95/2.52  res_num_sel_changes:                    0
% 15.95/2.52  res_moves_from_active_to_pass:          0
% 15.95/2.52  
% 15.95/2.52  ------ Superposition
% 15.95/2.52  
% 15.95/2.52  sup_time_total:                         0.
% 15.95/2.52  sup_time_generating:                    0.
% 15.95/2.52  sup_time_sim_full:                      0.
% 15.95/2.52  sup_time_sim_immed:                     0.
% 15.95/2.52  
% 15.95/2.52  sup_num_of_clauses:                     2372
% 15.95/2.52  sup_num_in_active:                      464
% 15.95/2.52  sup_num_in_passive:                     1908
% 15.95/2.52  sup_num_of_loops:                       564
% 15.95/2.52  sup_fw_superposition:                   2929
% 15.95/2.52  sup_bw_superposition:                   810
% 15.95/2.52  sup_immediate_simplified:               1560
% 15.95/2.52  sup_given_eliminated:                   1
% 15.95/2.52  comparisons_done:                       0
% 15.95/2.52  comparisons_avoided:                    9
% 15.95/2.52  
% 15.95/2.52  ------ Simplifications
% 15.95/2.52  
% 15.95/2.52  
% 15.95/2.52  sim_fw_subset_subsumed:                 12
% 15.95/2.52  sim_bw_subset_subsumed:                 33
% 15.95/2.52  sim_fw_subsumed:                        170
% 15.95/2.52  sim_bw_subsumed:                        2
% 15.95/2.52  sim_fw_subsumption_res:                 0
% 15.95/2.52  sim_bw_subsumption_res:                 0
% 15.95/2.52  sim_tautology_del:                      32
% 15.95/2.52  sim_eq_tautology_del:                   893
% 15.95/2.52  sim_eq_res_simp:                        0
% 15.95/2.52  sim_fw_demodulated:                     485
% 15.95/2.52  sim_bw_demodulated:                     91
% 15.95/2.52  sim_light_normalised:                   1171
% 15.95/2.52  sim_joinable_taut:                      0
% 15.95/2.52  sim_joinable_simp:                      0
% 15.95/2.52  sim_ac_normalised:                      0
% 15.95/2.52  sim_smt_subsumption:                    0
% 15.95/2.52  
%------------------------------------------------------------------------------
