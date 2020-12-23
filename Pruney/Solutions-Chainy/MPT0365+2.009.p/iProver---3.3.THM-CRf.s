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
% DateTime   : Thu Dec  3 11:40:46 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 411 expanded)
%              Number of clauses        :   85 ( 162 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  235 ( 999 expanded)
%              Number of equality atoms :  157 ( 469 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK2) != X1
        & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK2))
        & r1_xboole_0(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,X2) != sK1
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_subset_1(sK0,sK2) != sK1
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f40,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f42,plain,(
    k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_571,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_576,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10575,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_571,c_576])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11074,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10575,c_575])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_15111,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11074,c_18])).

cnf(c_15115,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_15111,c_576])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_574,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10568,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_571,c_574])).

cnf(c_10900,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_10568,c_10568,c_10575])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_573,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_577,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1465,plain,
    ( k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_573,c_577])).

cnf(c_11013,plain,
    ( k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10575,c_1465])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_570,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10576,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_570,c_576])).

cnf(c_11019,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11013,c_10576])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_579,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1657,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_579])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_580,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2255,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1657,c_580])).

cnf(c_2256,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2255,c_3])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_572,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_578,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1580,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_572,c_578])).

cnf(c_5,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_954,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_959,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_954,c_3])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1451,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_959,c_2])).

cnf(c_1798,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1580,c_1451])).

cnf(c_2265,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2256,c_1798])).

cnf(c_2267,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2265,c_3])).

cnf(c_2279,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2256,c_5])).

cnf(c_865,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_872,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_865,c_3])).

cnf(c_2264,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2256,c_872])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_779,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_780,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_779,c_3])).

cnf(c_952,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_780,c_5])).

cnf(c_2268,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2264,c_3,c_952])).

cnf(c_2288,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2279,c_3,c_2268])).

cnf(c_2902,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_2288,c_2])).

cnf(c_951,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_2912,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_2902,c_3,c_951,c_2256])).

cnf(c_4141,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK2)) = X0 ),
    inference(superposition,[status(thm)],[c_2267,c_2912])).

cnf(c_11020,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11019,c_4141])).

cnf(c_15118,plain,
    ( k4_xboole_0(sK0,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_15115,c_10900,c_11020])).

cnf(c_16546,plain,
    ( k3_subset_1(sK0,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_15118,c_10576])).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2130,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_262,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_812,plain,
    ( k3_subset_1(X0,sK1) != X1
    | sK2 != X1
    | sK2 = k3_subset_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1467,plain,
    ( k3_subset_1(X0,sK1) != sK2
    | sK2 = k3_subset_1(X0,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1468,plain,
    ( k3_subset_1(sK0,sK1) != sK2
    | sK2 = k3_subset_1(sK0,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_266,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_700,plain,
    ( k3_subset_1(sK0,sK2) = k3_subset_1(X0,k3_subset_1(X0,sK1))
    | sK2 != k3_subset_1(X0,sK1)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_701,plain,
    ( k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK2 != k3_subset_1(sK0,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_598,plain,
    ( k3_subset_1(sK0,sK2) != X0
    | k3_subset_1(sK0,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_680,plain,
    ( k3_subset_1(sK0,sK2) != k3_subset_1(X0,k3_subset_1(X0,sK1))
    | k3_subset_1(sK0,sK2) = sK1
    | sK1 != k3_subset_1(X0,k3_subset_1(X0,sK1)) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_681,plain,
    ( k3_subset_1(sK0,sK2) != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,sK2) = sK1
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_637,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_639,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_601,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_602,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_616,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK1)) != sK1
    | sK1 = k3_subset_1(X0,k3_subset_1(X0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_617,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != sK1
    | sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_606,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_276,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_12,negated_conjecture,
    ( k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16546,c_2130,c_1468,c_701,c_681,c_639,c_617,c_606,c_276,c_12,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.74/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.50  
% 7.74/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.50  
% 7.74/1.50  ------  iProver source info
% 7.74/1.50  
% 7.74/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.50  git: non_committed_changes: false
% 7.74/1.50  git: last_make_outside_of_git: false
% 7.74/1.50  
% 7.74/1.50  ------ 
% 7.74/1.50  
% 7.74/1.50  ------ Input Options
% 7.74/1.50  
% 7.74/1.50  --out_options                           all
% 7.74/1.50  --tptp_safe_out                         true
% 7.74/1.50  --problem_path                          ""
% 7.74/1.50  --include_path                          ""
% 7.74/1.50  --clausifier                            res/vclausify_rel
% 7.74/1.50  --clausifier_options                    ""
% 7.74/1.50  --stdin                                 false
% 7.74/1.50  --stats_out                             all
% 7.74/1.50  
% 7.74/1.50  ------ General Options
% 7.74/1.50  
% 7.74/1.50  --fof                                   false
% 7.74/1.50  --time_out_real                         305.
% 7.74/1.50  --time_out_virtual                      -1.
% 7.74/1.50  --symbol_type_check                     false
% 7.74/1.50  --clausify_out                          false
% 7.74/1.50  --sig_cnt_out                           false
% 7.74/1.50  --trig_cnt_out                          false
% 7.74/1.50  --trig_cnt_out_tolerance                1.
% 7.74/1.50  --trig_cnt_out_sk_spl                   false
% 7.74/1.50  --abstr_cl_out                          false
% 7.74/1.50  
% 7.74/1.50  ------ Global Options
% 7.74/1.50  
% 7.74/1.50  --schedule                              default
% 7.74/1.50  --add_important_lit                     false
% 7.74/1.50  --prop_solver_per_cl                    1000
% 7.74/1.50  --min_unsat_core                        false
% 7.74/1.50  --soft_assumptions                      false
% 7.74/1.50  --soft_lemma_size                       3
% 7.74/1.50  --prop_impl_unit_size                   0
% 7.74/1.50  --prop_impl_unit                        []
% 7.74/1.50  --share_sel_clauses                     true
% 7.74/1.50  --reset_solvers                         false
% 7.74/1.50  --bc_imp_inh                            [conj_cone]
% 7.74/1.50  --conj_cone_tolerance                   3.
% 7.74/1.50  --extra_neg_conj                        none
% 7.74/1.50  --large_theory_mode                     true
% 7.74/1.50  --prolific_symb_bound                   200
% 7.74/1.50  --lt_threshold                          2000
% 7.74/1.50  --clause_weak_htbl                      true
% 7.74/1.50  --gc_record_bc_elim                     false
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing Options
% 7.74/1.50  
% 7.74/1.50  --preprocessing_flag                    true
% 7.74/1.50  --time_out_prep_mult                    0.1
% 7.74/1.50  --splitting_mode                        input
% 7.74/1.50  --splitting_grd                         true
% 7.74/1.50  --splitting_cvd                         false
% 7.74/1.50  --splitting_cvd_svl                     false
% 7.74/1.50  --splitting_nvd                         32
% 7.74/1.50  --sub_typing                            true
% 7.74/1.50  --prep_gs_sim                           true
% 7.74/1.50  --prep_unflatten                        true
% 7.74/1.50  --prep_res_sim                          true
% 7.74/1.50  --prep_upred                            true
% 7.74/1.50  --prep_sem_filter                       exhaustive
% 7.74/1.50  --prep_sem_filter_out                   false
% 7.74/1.50  --pred_elim                             true
% 7.74/1.50  --res_sim_input                         true
% 7.74/1.50  --eq_ax_congr_red                       true
% 7.74/1.50  --pure_diseq_elim                       true
% 7.74/1.50  --brand_transform                       false
% 7.74/1.50  --non_eq_to_eq                          false
% 7.74/1.50  --prep_def_merge                        true
% 7.74/1.50  --prep_def_merge_prop_impl              false
% 7.74/1.50  --prep_def_merge_mbd                    true
% 7.74/1.50  --prep_def_merge_tr_red                 false
% 7.74/1.50  --prep_def_merge_tr_cl                  false
% 7.74/1.50  --smt_preprocessing                     true
% 7.74/1.50  --smt_ac_axioms                         fast
% 7.74/1.50  --preprocessed_out                      false
% 7.74/1.50  --preprocessed_stats                    false
% 7.74/1.50  
% 7.74/1.50  ------ Abstraction refinement Options
% 7.74/1.50  
% 7.74/1.50  --abstr_ref                             []
% 7.74/1.50  --abstr_ref_prep                        false
% 7.74/1.50  --abstr_ref_until_sat                   false
% 7.74/1.50  --abstr_ref_sig_restrict                funpre
% 7.74/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.50  --abstr_ref_under                       []
% 7.74/1.50  
% 7.74/1.50  ------ SAT Options
% 7.74/1.50  
% 7.74/1.50  --sat_mode                              false
% 7.74/1.50  --sat_fm_restart_options                ""
% 7.74/1.50  --sat_gr_def                            false
% 7.74/1.50  --sat_epr_types                         true
% 7.74/1.50  --sat_non_cyclic_types                  false
% 7.74/1.50  --sat_finite_models                     false
% 7.74/1.50  --sat_fm_lemmas                         false
% 7.74/1.50  --sat_fm_prep                           false
% 7.74/1.50  --sat_fm_uc_incr                        true
% 7.74/1.50  --sat_out_model                         small
% 7.74/1.50  --sat_out_clauses                       false
% 7.74/1.50  
% 7.74/1.50  ------ QBF Options
% 7.74/1.50  
% 7.74/1.50  --qbf_mode                              false
% 7.74/1.50  --qbf_elim_univ                         false
% 7.74/1.50  --qbf_dom_inst                          none
% 7.74/1.50  --qbf_dom_pre_inst                      false
% 7.74/1.50  --qbf_sk_in                             false
% 7.74/1.50  --qbf_pred_elim                         true
% 7.74/1.50  --qbf_split                             512
% 7.74/1.50  
% 7.74/1.50  ------ BMC1 Options
% 7.74/1.50  
% 7.74/1.50  --bmc1_incremental                      false
% 7.74/1.50  --bmc1_axioms                           reachable_all
% 7.74/1.50  --bmc1_min_bound                        0
% 7.74/1.50  --bmc1_max_bound                        -1
% 7.74/1.50  --bmc1_max_bound_default                -1
% 7.74/1.50  --bmc1_symbol_reachability              true
% 7.74/1.50  --bmc1_property_lemmas                  false
% 7.74/1.50  --bmc1_k_induction                      false
% 7.74/1.50  --bmc1_non_equiv_states                 false
% 7.74/1.50  --bmc1_deadlock                         false
% 7.74/1.50  --bmc1_ucm                              false
% 7.74/1.50  --bmc1_add_unsat_core                   none
% 7.74/1.50  --bmc1_unsat_core_children              false
% 7.74/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.50  --bmc1_out_stat                         full
% 7.74/1.50  --bmc1_ground_init                      false
% 7.74/1.50  --bmc1_pre_inst_next_state              false
% 7.74/1.50  --bmc1_pre_inst_state                   false
% 7.74/1.50  --bmc1_pre_inst_reach_state             false
% 7.74/1.50  --bmc1_out_unsat_core                   false
% 7.74/1.50  --bmc1_aig_witness_out                  false
% 7.74/1.50  --bmc1_verbose                          false
% 7.74/1.50  --bmc1_dump_clauses_tptp                false
% 7.74/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.50  --bmc1_dump_file                        -
% 7.74/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.50  --bmc1_ucm_extend_mode                  1
% 7.74/1.50  --bmc1_ucm_init_mode                    2
% 7.74/1.50  --bmc1_ucm_cone_mode                    none
% 7.74/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.50  --bmc1_ucm_relax_model                  4
% 7.74/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.50  --bmc1_ucm_layered_model                none
% 7.74/1.50  --bmc1_ucm_max_lemma_size               10
% 7.74/1.50  
% 7.74/1.50  ------ AIG Options
% 7.74/1.50  
% 7.74/1.50  --aig_mode                              false
% 7.74/1.50  
% 7.74/1.50  ------ Instantiation Options
% 7.74/1.50  
% 7.74/1.50  --instantiation_flag                    true
% 7.74/1.50  --inst_sos_flag                         true
% 7.74/1.50  --inst_sos_phase                        true
% 7.74/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.50  --inst_lit_sel_side                     num_symb
% 7.74/1.50  --inst_solver_per_active                1400
% 7.74/1.50  --inst_solver_calls_frac                1.
% 7.74/1.50  --inst_passive_queue_type               priority_queues
% 7.74/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.50  --inst_passive_queues_freq              [25;2]
% 7.74/1.50  --inst_dismatching                      true
% 7.74/1.50  --inst_eager_unprocessed_to_passive     true
% 7.74/1.50  --inst_prop_sim_given                   true
% 7.74/1.50  --inst_prop_sim_new                     false
% 7.74/1.50  --inst_subs_new                         false
% 7.74/1.50  --inst_eq_res_simp                      false
% 7.74/1.50  --inst_subs_given                       false
% 7.74/1.50  --inst_orphan_elimination               true
% 7.74/1.50  --inst_learning_loop_flag               true
% 7.74/1.50  --inst_learning_start                   3000
% 7.74/1.50  --inst_learning_factor                  2
% 7.74/1.50  --inst_start_prop_sim_after_learn       3
% 7.74/1.50  --inst_sel_renew                        solver
% 7.74/1.50  --inst_lit_activity_flag                true
% 7.74/1.50  --inst_restr_to_given                   false
% 7.74/1.50  --inst_activity_threshold               500
% 7.74/1.50  --inst_out_proof                        true
% 7.74/1.50  
% 7.74/1.50  ------ Resolution Options
% 7.74/1.50  
% 7.74/1.50  --resolution_flag                       true
% 7.74/1.50  --res_lit_sel                           adaptive
% 7.74/1.50  --res_lit_sel_side                      none
% 7.74/1.50  --res_ordering                          kbo
% 7.74/1.50  --res_to_prop_solver                    active
% 7.74/1.50  --res_prop_simpl_new                    false
% 7.74/1.50  --res_prop_simpl_given                  true
% 7.74/1.50  --res_passive_queue_type                priority_queues
% 7.74/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.50  --res_passive_queues_freq               [15;5]
% 7.74/1.50  --res_forward_subs                      full
% 7.74/1.50  --res_backward_subs                     full
% 7.74/1.50  --res_forward_subs_resolution           true
% 7.74/1.50  --res_backward_subs_resolution          true
% 7.74/1.50  --res_orphan_elimination                true
% 7.74/1.50  --res_time_limit                        2.
% 7.74/1.50  --res_out_proof                         true
% 7.74/1.50  
% 7.74/1.50  ------ Superposition Options
% 7.74/1.50  
% 7.74/1.50  --superposition_flag                    true
% 7.74/1.50  --sup_passive_queue_type                priority_queues
% 7.74/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.50  --demod_completeness_check              fast
% 7.74/1.50  --demod_use_ground                      true
% 7.74/1.50  --sup_to_prop_solver                    passive
% 7.74/1.50  --sup_prop_simpl_new                    true
% 7.74/1.50  --sup_prop_simpl_given                  true
% 7.74/1.50  --sup_fun_splitting                     true
% 7.74/1.50  --sup_smt_interval                      50000
% 7.74/1.50  
% 7.74/1.50  ------ Superposition Simplification Setup
% 7.74/1.50  
% 7.74/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.50  --sup_immed_triv                        [TrivRules]
% 7.74/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_immed_bw_main                     []
% 7.74/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_input_bw                          []
% 7.74/1.50  
% 7.74/1.50  ------ Combination Options
% 7.74/1.50  
% 7.74/1.50  --comb_res_mult                         3
% 7.74/1.50  --comb_sup_mult                         2
% 7.74/1.50  --comb_inst_mult                        10
% 7.74/1.50  
% 7.74/1.50  ------ Debug Options
% 7.74/1.50  
% 7.74/1.50  --dbg_backtrace                         false
% 7.74/1.50  --dbg_dump_prop_clauses                 false
% 7.74/1.50  --dbg_dump_prop_clauses_file            -
% 7.74/1.50  --dbg_out_stat                          false
% 7.74/1.50  ------ Parsing...
% 7.74/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.50  ------ Proving...
% 7.74/1.50  ------ Problem Properties 
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  clauses                                 17
% 7.74/1.50  conjectures                             5
% 7.74/1.50  EPR                                     1
% 7.74/1.50  Horn                                    17
% 7.74/1.50  unary                                   9
% 7.74/1.50  binary                                  8
% 7.74/1.50  lits                                    25
% 7.74/1.50  lits eq                                 12
% 7.74/1.50  fd_pure                                 0
% 7.74/1.50  fd_pseudo                               0
% 7.74/1.50  fd_cond                                 0
% 7.74/1.50  fd_pseudo_cond                          0
% 7.74/1.50  AC symbols                              0
% 7.74/1.50  
% 7.74/1.50  ------ Schedule dynamic 5 is on 
% 7.74/1.50  
% 7.74/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  ------ 
% 7.74/1.50  Current options:
% 7.74/1.50  ------ 
% 7.74/1.50  
% 7.74/1.50  ------ Input Options
% 7.74/1.50  
% 7.74/1.50  --out_options                           all
% 7.74/1.50  --tptp_safe_out                         true
% 7.74/1.50  --problem_path                          ""
% 7.74/1.50  --include_path                          ""
% 7.74/1.50  --clausifier                            res/vclausify_rel
% 7.74/1.50  --clausifier_options                    ""
% 7.74/1.50  --stdin                                 false
% 7.74/1.50  --stats_out                             all
% 7.74/1.50  
% 7.74/1.50  ------ General Options
% 7.74/1.50  
% 7.74/1.50  --fof                                   false
% 7.74/1.50  --time_out_real                         305.
% 7.74/1.50  --time_out_virtual                      -1.
% 7.74/1.50  --symbol_type_check                     false
% 7.74/1.50  --clausify_out                          false
% 7.74/1.50  --sig_cnt_out                           false
% 7.74/1.50  --trig_cnt_out                          false
% 7.74/1.50  --trig_cnt_out_tolerance                1.
% 7.74/1.50  --trig_cnt_out_sk_spl                   false
% 7.74/1.50  --abstr_cl_out                          false
% 7.74/1.50  
% 7.74/1.50  ------ Global Options
% 7.74/1.50  
% 7.74/1.50  --schedule                              default
% 7.74/1.50  --add_important_lit                     false
% 7.74/1.50  --prop_solver_per_cl                    1000
% 7.74/1.50  --min_unsat_core                        false
% 7.74/1.50  --soft_assumptions                      false
% 7.74/1.50  --soft_lemma_size                       3
% 7.74/1.50  --prop_impl_unit_size                   0
% 7.74/1.50  --prop_impl_unit                        []
% 7.74/1.50  --share_sel_clauses                     true
% 7.74/1.50  --reset_solvers                         false
% 7.74/1.50  --bc_imp_inh                            [conj_cone]
% 7.74/1.50  --conj_cone_tolerance                   3.
% 7.74/1.50  --extra_neg_conj                        none
% 7.74/1.50  --large_theory_mode                     true
% 7.74/1.50  --prolific_symb_bound                   200
% 7.74/1.50  --lt_threshold                          2000
% 7.74/1.50  --clause_weak_htbl                      true
% 7.74/1.50  --gc_record_bc_elim                     false
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing Options
% 7.74/1.50  
% 7.74/1.50  --preprocessing_flag                    true
% 7.74/1.50  --time_out_prep_mult                    0.1
% 7.74/1.50  --splitting_mode                        input
% 7.74/1.50  --splitting_grd                         true
% 7.74/1.50  --splitting_cvd                         false
% 7.74/1.50  --splitting_cvd_svl                     false
% 7.74/1.50  --splitting_nvd                         32
% 7.74/1.50  --sub_typing                            true
% 7.74/1.50  --prep_gs_sim                           true
% 7.74/1.50  --prep_unflatten                        true
% 7.74/1.50  --prep_res_sim                          true
% 7.74/1.50  --prep_upred                            true
% 7.74/1.50  --prep_sem_filter                       exhaustive
% 7.74/1.50  --prep_sem_filter_out                   false
% 7.74/1.50  --pred_elim                             true
% 7.74/1.50  --res_sim_input                         true
% 7.74/1.50  --eq_ax_congr_red                       true
% 7.74/1.50  --pure_diseq_elim                       true
% 7.74/1.50  --brand_transform                       false
% 7.74/1.50  --non_eq_to_eq                          false
% 7.74/1.50  --prep_def_merge                        true
% 7.74/1.50  --prep_def_merge_prop_impl              false
% 7.74/1.50  --prep_def_merge_mbd                    true
% 7.74/1.50  --prep_def_merge_tr_red                 false
% 7.74/1.50  --prep_def_merge_tr_cl                  false
% 7.74/1.50  --smt_preprocessing                     true
% 7.74/1.50  --smt_ac_axioms                         fast
% 7.74/1.50  --preprocessed_out                      false
% 7.74/1.50  --preprocessed_stats                    false
% 7.74/1.50  
% 7.74/1.50  ------ Abstraction refinement Options
% 7.74/1.50  
% 7.74/1.50  --abstr_ref                             []
% 7.74/1.50  --abstr_ref_prep                        false
% 7.74/1.50  --abstr_ref_until_sat                   false
% 7.74/1.50  --abstr_ref_sig_restrict                funpre
% 7.74/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.50  --abstr_ref_under                       []
% 7.74/1.50  
% 7.74/1.50  ------ SAT Options
% 7.74/1.50  
% 7.74/1.50  --sat_mode                              false
% 7.74/1.50  --sat_fm_restart_options                ""
% 7.74/1.50  --sat_gr_def                            false
% 7.74/1.50  --sat_epr_types                         true
% 7.74/1.50  --sat_non_cyclic_types                  false
% 7.74/1.50  --sat_finite_models                     false
% 7.74/1.50  --sat_fm_lemmas                         false
% 7.74/1.50  --sat_fm_prep                           false
% 7.74/1.50  --sat_fm_uc_incr                        true
% 7.74/1.50  --sat_out_model                         small
% 7.74/1.50  --sat_out_clauses                       false
% 7.74/1.50  
% 7.74/1.50  ------ QBF Options
% 7.74/1.50  
% 7.74/1.50  --qbf_mode                              false
% 7.74/1.50  --qbf_elim_univ                         false
% 7.74/1.50  --qbf_dom_inst                          none
% 7.74/1.50  --qbf_dom_pre_inst                      false
% 7.74/1.50  --qbf_sk_in                             false
% 7.74/1.50  --qbf_pred_elim                         true
% 7.74/1.50  --qbf_split                             512
% 7.74/1.50  
% 7.74/1.50  ------ BMC1 Options
% 7.74/1.50  
% 7.74/1.50  --bmc1_incremental                      false
% 7.74/1.50  --bmc1_axioms                           reachable_all
% 7.74/1.50  --bmc1_min_bound                        0
% 7.74/1.50  --bmc1_max_bound                        -1
% 7.74/1.50  --bmc1_max_bound_default                -1
% 7.74/1.50  --bmc1_symbol_reachability              true
% 7.74/1.50  --bmc1_property_lemmas                  false
% 7.74/1.50  --bmc1_k_induction                      false
% 7.74/1.50  --bmc1_non_equiv_states                 false
% 7.74/1.50  --bmc1_deadlock                         false
% 7.74/1.50  --bmc1_ucm                              false
% 7.74/1.50  --bmc1_add_unsat_core                   none
% 7.74/1.50  --bmc1_unsat_core_children              false
% 7.74/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.50  --bmc1_out_stat                         full
% 7.74/1.50  --bmc1_ground_init                      false
% 7.74/1.50  --bmc1_pre_inst_next_state              false
% 7.74/1.50  --bmc1_pre_inst_state                   false
% 7.74/1.50  --bmc1_pre_inst_reach_state             false
% 7.74/1.50  --bmc1_out_unsat_core                   false
% 7.74/1.50  --bmc1_aig_witness_out                  false
% 7.74/1.50  --bmc1_verbose                          false
% 7.74/1.50  --bmc1_dump_clauses_tptp                false
% 7.74/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.50  --bmc1_dump_file                        -
% 7.74/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.50  --bmc1_ucm_extend_mode                  1
% 7.74/1.50  --bmc1_ucm_init_mode                    2
% 7.74/1.50  --bmc1_ucm_cone_mode                    none
% 7.74/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.50  --bmc1_ucm_relax_model                  4
% 7.74/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.50  --bmc1_ucm_layered_model                none
% 7.74/1.50  --bmc1_ucm_max_lemma_size               10
% 7.74/1.50  
% 7.74/1.50  ------ AIG Options
% 7.74/1.50  
% 7.74/1.50  --aig_mode                              false
% 7.74/1.50  
% 7.74/1.50  ------ Instantiation Options
% 7.74/1.50  
% 7.74/1.50  --instantiation_flag                    true
% 7.74/1.50  --inst_sos_flag                         true
% 7.74/1.50  --inst_sos_phase                        true
% 7.74/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.50  --inst_lit_sel_side                     none
% 7.74/1.50  --inst_solver_per_active                1400
% 7.74/1.50  --inst_solver_calls_frac                1.
% 7.74/1.50  --inst_passive_queue_type               priority_queues
% 7.74/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.50  --inst_passive_queues_freq              [25;2]
% 7.74/1.50  --inst_dismatching                      true
% 7.74/1.50  --inst_eager_unprocessed_to_passive     true
% 7.74/1.50  --inst_prop_sim_given                   true
% 7.74/1.50  --inst_prop_sim_new                     false
% 7.74/1.50  --inst_subs_new                         false
% 7.74/1.50  --inst_eq_res_simp                      false
% 7.74/1.50  --inst_subs_given                       false
% 7.74/1.50  --inst_orphan_elimination               true
% 7.74/1.50  --inst_learning_loop_flag               true
% 7.74/1.50  --inst_learning_start                   3000
% 7.74/1.50  --inst_learning_factor                  2
% 7.74/1.50  --inst_start_prop_sim_after_learn       3
% 7.74/1.50  --inst_sel_renew                        solver
% 7.74/1.50  --inst_lit_activity_flag                true
% 7.74/1.50  --inst_restr_to_given                   false
% 7.74/1.50  --inst_activity_threshold               500
% 7.74/1.50  --inst_out_proof                        true
% 7.74/1.50  
% 7.74/1.50  ------ Resolution Options
% 7.74/1.50  
% 7.74/1.50  --resolution_flag                       false
% 7.74/1.50  --res_lit_sel                           adaptive
% 7.74/1.50  --res_lit_sel_side                      none
% 7.74/1.50  --res_ordering                          kbo
% 7.74/1.50  --res_to_prop_solver                    active
% 7.74/1.50  --res_prop_simpl_new                    false
% 7.74/1.50  --res_prop_simpl_given                  true
% 7.74/1.50  --res_passive_queue_type                priority_queues
% 7.74/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.50  --res_passive_queues_freq               [15;5]
% 7.74/1.50  --res_forward_subs                      full
% 7.74/1.50  --res_backward_subs                     full
% 7.74/1.50  --res_forward_subs_resolution           true
% 7.74/1.50  --res_backward_subs_resolution          true
% 7.74/1.50  --res_orphan_elimination                true
% 7.74/1.50  --res_time_limit                        2.
% 7.74/1.50  --res_out_proof                         true
% 7.74/1.50  
% 7.74/1.50  ------ Superposition Options
% 7.74/1.50  
% 7.74/1.50  --superposition_flag                    true
% 7.74/1.50  --sup_passive_queue_type                priority_queues
% 7.74/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.50  --demod_completeness_check              fast
% 7.74/1.50  --demod_use_ground                      true
% 7.74/1.50  --sup_to_prop_solver                    passive
% 7.74/1.50  --sup_prop_simpl_new                    true
% 7.74/1.50  --sup_prop_simpl_given                  true
% 7.74/1.50  --sup_fun_splitting                     true
% 7.74/1.50  --sup_smt_interval                      50000
% 7.74/1.50  
% 7.74/1.50  ------ Superposition Simplification Setup
% 7.74/1.50  
% 7.74/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.50  --sup_immed_triv                        [TrivRules]
% 7.74/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_immed_bw_main                     []
% 7.74/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.50  --sup_input_bw                          []
% 7.74/1.50  
% 7.74/1.50  ------ Combination Options
% 7.74/1.50  
% 7.74/1.50  --comb_res_mult                         3
% 7.74/1.50  --comb_sup_mult                         2
% 7.74/1.50  --comb_inst_mult                        10
% 7.74/1.50  
% 7.74/1.50  ------ Debug Options
% 7.74/1.50  
% 7.74/1.50  --dbg_backtrace                         false
% 7.74/1.50  --dbg_dump_prop_clauses                 false
% 7.74/1.50  --dbg_dump_prop_clauses_file            -
% 7.74/1.50  --dbg_out_stat                          false
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  ------ Proving...
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  % SZS status Theorem for theBenchmark.p
% 7.74/1.50  
% 7.74/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.50  
% 7.74/1.50  fof(f12,conjecture,(
% 7.74/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f13,negated_conjecture,(
% 7.74/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 7.74/1.50    inference(negated_conjecture,[],[f12])).
% 7.74/1.50  
% 7.74/1.50  fof(f18,plain,(
% 7.74/1.50    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.50    inference(ennf_transformation,[],[f13])).
% 7.74/1.50  
% 7.74/1.50  fof(f19,plain,(
% 7.74/1.50    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.50    inference(flattening,[],[f18])).
% 7.74/1.50  
% 7.74/1.50  fof(f23,plain,(
% 7.74/1.50    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK2)) & r1_xboole_0(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 7.74/1.50    introduced(choice_axiom,[])).
% 7.74/1.50  
% 7.74/1.50  fof(f22,plain,(
% 7.74/1.50    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK0,X2) != sK1 & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.74/1.50    introduced(choice_axiom,[])).
% 7.74/1.50  
% 7.74/1.50  fof(f24,plain,(
% 7.74/1.50    (k3_subset_1(sK0,sK2) != sK1 & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.74/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22])).
% 7.74/1.50  
% 7.74/1.50  fof(f39,plain,(
% 7.74/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.74/1.50    inference(cnf_transformation,[],[f24])).
% 7.74/1.50  
% 7.74/1.50  fof(f9,axiom,(
% 7.74/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f15,plain,(
% 7.74/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.50    inference(ennf_transformation,[],[f9])).
% 7.74/1.50  
% 7.74/1.50  fof(f35,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f15])).
% 7.74/1.50  
% 7.74/1.50  fof(f10,axiom,(
% 7.74/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f16,plain,(
% 7.74/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.50    inference(ennf_transformation,[],[f10])).
% 7.74/1.50  
% 7.74/1.50  fof(f36,plain,(
% 7.74/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f16])).
% 7.74/1.50  
% 7.74/1.50  fof(f11,axiom,(
% 7.74/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f17,plain,(
% 7.74/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.50    inference(ennf_transformation,[],[f11])).
% 7.74/1.50  
% 7.74/1.50  fof(f37,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f17])).
% 7.74/1.50  
% 7.74/1.50  fof(f41,plain,(
% 7.74/1.50    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 7.74/1.50    inference(cnf_transformation,[],[f24])).
% 7.74/1.50  
% 7.74/1.50  fof(f8,axiom,(
% 7.74/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f14,plain,(
% 7.74/1.50    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 7.74/1.50    inference(ennf_transformation,[],[f8])).
% 7.74/1.50  
% 7.74/1.50  fof(f34,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.50    inference(cnf_transformation,[],[f14])).
% 7.74/1.50  
% 7.74/1.50  fof(f38,plain,(
% 7.74/1.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.74/1.50    inference(cnf_transformation,[],[f24])).
% 7.74/1.50  
% 7.74/1.50  fof(f3,axiom,(
% 7.74/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f28,plain,(
% 7.74/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.74/1.50    inference(cnf_transformation,[],[f3])).
% 7.74/1.50  
% 7.74/1.50  fof(f7,axiom,(
% 7.74/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f21,plain,(
% 7.74/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.74/1.50    inference(nnf_transformation,[],[f7])).
% 7.74/1.50  
% 7.74/1.50  fof(f33,plain,(
% 7.74/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.74/1.50    inference(cnf_transformation,[],[f21])).
% 7.74/1.50  
% 7.74/1.50  fof(f1,axiom,(
% 7.74/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f20,plain,(
% 7.74/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.74/1.50    inference(nnf_transformation,[],[f1])).
% 7.74/1.50  
% 7.74/1.50  fof(f25,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.50    inference(cnf_transformation,[],[f20])).
% 7.74/1.50  
% 7.74/1.50  fof(f5,axiom,(
% 7.74/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f30,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f5])).
% 7.74/1.50  
% 7.74/1.50  fof(f44,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.50    inference(definition_unfolding,[],[f25,f30])).
% 7.74/1.50  
% 7.74/1.50  fof(f40,plain,(
% 7.74/1.50    r1_xboole_0(sK1,sK2)),
% 7.74/1.50    inference(cnf_transformation,[],[f24])).
% 7.74/1.50  
% 7.74/1.50  fof(f32,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.50    inference(cnf_transformation,[],[f21])).
% 7.74/1.50  
% 7.74/1.50  fof(f6,axiom,(
% 7.74/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f31,plain,(
% 7.74/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f6])).
% 7.74/1.50  
% 7.74/1.50  fof(f47,plain,(
% 7.74/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.74/1.50    inference(definition_unfolding,[],[f31,f30])).
% 7.74/1.50  
% 7.74/1.50  fof(f2,axiom,(
% 7.74/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f27,plain,(
% 7.74/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f2])).
% 7.74/1.50  
% 7.74/1.50  fof(f45,plain,(
% 7.74/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 7.74/1.50    inference(definition_unfolding,[],[f27,f30])).
% 7.74/1.50  
% 7.74/1.50  fof(f4,axiom,(
% 7.74/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.74/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.50  
% 7.74/1.50  fof(f29,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.74/1.50    inference(cnf_transformation,[],[f4])).
% 7.74/1.50  
% 7.74/1.50  fof(f46,plain,(
% 7.74/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.74/1.50    inference(definition_unfolding,[],[f29,f30])).
% 7.74/1.50  
% 7.74/1.50  fof(f42,plain,(
% 7.74/1.50    k3_subset_1(sK0,sK2) != sK1),
% 7.74/1.50    inference(cnf_transformation,[],[f24])).
% 7.74/1.50  
% 7.74/1.50  cnf(c_15,negated_conjecture,
% 7.74/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.74/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_571,plain,
% 7.74/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_9,plain,
% 7.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.74/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_576,plain,
% 7.74/1.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.74/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_10575,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_571,c_576]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_10,plain,
% 7.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.74/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_575,plain,
% 7.74/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.74/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_11074,plain,
% 7.74/1.50      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 7.74/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_10575,c_575]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_18,plain,
% 7.74/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_15111,plain,
% 7.74/1.50      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 7.74/1.50      inference(global_propositional_subsumption,
% 7.74/1.50                [status(thm)],
% 7.74/1.50                [c_11074,c_18]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_15115,plain,
% 7.74/1.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_15111,c_576]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_11,plain,
% 7.74/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_574,plain,
% 7.74/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.74/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_10568,plain,
% 7.74/1.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_571,c_574]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_10900,plain,
% 7.74/1.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 7.74/1.50      inference(light_normalisation,
% 7.74/1.50                [status(thm)],
% 7.74/1.50                [c_10568,c_10568,c_10575]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_13,negated_conjecture,
% 7.74/1.50      ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
% 7.74/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_573,plain,
% 7.74/1.50      ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_8,plain,
% 7.74/1.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_577,plain,
% 7.74/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
% 7.74/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1465,plain,
% 7.74/1.50      ( k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_573,c_577]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_11013,plain,
% 7.74/1.50      ( k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_10575,c_1465]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_16,negated_conjecture,
% 7.74/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 7.74/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_570,plain,
% 7.74/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_10576,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_570,c_576]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_11019,plain,
% 7.74/1.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_11013,c_10576]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_3,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_6,plain,
% 7.74/1.50      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_579,plain,
% 7.74/1.50      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1657,plain,
% 7.74/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_3,c_579]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1,plain,
% 7.74/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.74/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_580,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.74/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2255,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_1657,c_580]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2256,plain,
% 7.74/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_2255,c_3]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_14,negated_conjecture,
% 7.74/1.50      ( r1_xboole_0(sK1,sK2) ),
% 7.74/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_572,plain,
% 7.74/1.50      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_7,plain,
% 7.74/1.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.74/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_578,plain,
% 7.74/1.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.74/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1580,plain,
% 7.74/1.50      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_572,c_578]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_5,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.74/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_954,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_959,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X1) ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_954,c_3]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.74/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1451,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_959,c_2]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1798,plain,
% 7.74/1.50      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,sK1) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_1580,c_1451]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2265,plain,
% 7.74/1.50      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_2256,c_1798]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2267,plain,
% 7.74/1.50      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_2265,c_3]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2279,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_2256,c_5]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_865,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_872,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_865,c_3]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2264,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_2256,c_872]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_4,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.74/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_779,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_780,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_779,c_3]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_952,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_780,c_5]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2268,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_2264,c_3,c_952]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2288,plain,
% 7.74/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.74/1.50      inference(light_normalisation,[status(thm)],[c_2279,c_3,c_2268]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2902,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_2288,c_2]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_951,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2912,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_2902,c_3,c_951,c_2256]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_4141,plain,
% 7.74/1.50      ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK2)) = X0 ),
% 7.74/1.50      inference(superposition,[status(thm)],[c_2267,c_2912]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_11020,plain,
% 7.74/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_11019,c_4141]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_15118,plain,
% 7.74/1.50      ( k4_xboole_0(sK0,sK1) = sK2 ),
% 7.74/1.50      inference(light_normalisation,
% 7.74/1.50                [status(thm)],
% 7.74/1.50                [c_15115,c_10900,c_11020]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_16546,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK1) = sK2 ),
% 7.74/1.50      inference(demodulation,[status(thm)],[c_15118,c_10576]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_261,plain,( X0 = X0 ),theory(equality) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_2130,plain,
% 7.74/1.50      ( sK2 = sK2 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_261]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_262,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_812,plain,
% 7.74/1.50      ( k3_subset_1(X0,sK1) != X1
% 7.74/1.50      | sK2 != X1
% 7.74/1.50      | sK2 = k3_subset_1(X0,sK1) ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_262]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1467,plain,
% 7.74/1.50      ( k3_subset_1(X0,sK1) != sK2
% 7.74/1.50      | sK2 = k3_subset_1(X0,sK1)
% 7.74/1.50      | sK2 != sK2 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_812]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_1468,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK1) != sK2
% 7.74/1.50      | sK2 = k3_subset_1(sK0,sK1)
% 7.74/1.50      | sK2 != sK2 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_1467]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_266,plain,
% 7.74/1.50      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 7.74/1.50      theory(equality) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_700,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) = k3_subset_1(X0,k3_subset_1(X0,sK1))
% 7.74/1.50      | sK2 != k3_subset_1(X0,sK1)
% 7.74/1.50      | sK0 != X0 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_266]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_701,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.74/1.50      | sK2 != k3_subset_1(sK0,sK1)
% 7.74/1.50      | sK0 != sK0 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_700]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_598,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) != X0
% 7.74/1.50      | k3_subset_1(sK0,sK2) = sK1
% 7.74/1.50      | sK1 != X0 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_262]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_680,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) != k3_subset_1(X0,k3_subset_1(X0,sK1))
% 7.74/1.50      | k3_subset_1(sK0,sK2) = sK1
% 7.74/1.50      | sK1 != k3_subset_1(X0,k3_subset_1(X0,sK1)) ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_598]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_681,plain,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.74/1.50      | k3_subset_1(sK0,sK2) = sK1
% 7.74/1.50      | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_680]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_637,plain,
% 7.74/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
% 7.74/1.50      | k3_subset_1(X0,k3_subset_1(X0,sK1)) = sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_639,plain,
% 7.74/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 7.74/1.50      | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_637]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_601,plain,
% 7.74/1.50      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_262]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_602,plain,
% 7.74/1.50      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_601]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_616,plain,
% 7.74/1.50      ( k3_subset_1(X0,k3_subset_1(X0,sK1)) != sK1
% 7.74/1.50      | sK1 = k3_subset_1(X0,k3_subset_1(X0,sK1))
% 7.74/1.50      | sK1 != sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_602]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_617,plain,
% 7.74/1.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != sK1
% 7.74/1.50      | sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.74/1.50      | sK1 != sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_616]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_606,plain,
% 7.74/1.50      ( sK1 = sK1 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_261]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_276,plain,
% 7.74/1.50      ( sK0 = sK0 ),
% 7.74/1.50      inference(instantiation,[status(thm)],[c_261]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(c_12,negated_conjecture,
% 7.74/1.50      ( k3_subset_1(sK0,sK2) != sK1 ),
% 7.74/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.74/1.50  
% 7.74/1.50  cnf(contradiction,plain,
% 7.74/1.50      ( $false ),
% 7.74/1.50      inference(minisat,
% 7.74/1.50                [status(thm)],
% 7.74/1.50                [c_16546,c_2130,c_1468,c_701,c_681,c_639,c_617,c_606,
% 7.74/1.50                 c_276,c_12,c_16]) ).
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.50  
% 7.74/1.50  ------                               Statistics
% 7.74/1.50  
% 7.74/1.50  ------ General
% 7.74/1.50  
% 7.74/1.50  abstr_ref_over_cycles:                  0
% 7.74/1.50  abstr_ref_under_cycles:                 0
% 7.74/1.50  gc_basic_clause_elim:                   0
% 7.74/1.50  forced_gc_time:                         0
% 7.74/1.50  parsing_time:                           0.007
% 7.74/1.50  unif_index_cands_time:                  0.
% 7.74/1.50  unif_index_add_time:                    0.
% 7.74/1.50  orderings_time:                         0.
% 7.74/1.50  out_proof_time:                         0.012
% 7.74/1.50  total_time:                             0.631
% 7.74/1.50  num_of_symbols:                         41
% 7.74/1.50  num_of_terms:                           22730
% 7.74/1.50  
% 7.74/1.50  ------ Preprocessing
% 7.74/1.50  
% 7.74/1.50  num_of_splits:                          0
% 7.74/1.50  num_of_split_atoms:                     0
% 7.74/1.50  num_of_reused_defs:                     0
% 7.74/1.50  num_eq_ax_congr_red:                    0
% 7.74/1.50  num_of_sem_filtered_clauses:            1
% 7.74/1.50  num_of_subtypes:                        0
% 7.74/1.50  monotx_restored_types:                  0
% 7.74/1.50  sat_num_of_epr_types:                   0
% 7.74/1.50  sat_num_of_non_cyclic_types:            0
% 7.74/1.50  sat_guarded_non_collapsed_types:        0
% 7.74/1.50  num_pure_diseq_elim:                    0
% 7.74/1.50  simp_replaced_by:                       0
% 7.74/1.50  res_preprocessed:                       68
% 7.74/1.50  prep_upred:                             0
% 7.74/1.50  prep_unflattend:                        12
% 7.74/1.50  smt_new_axioms:                         0
% 7.74/1.50  pred_elim_cands:                        2
% 7.74/1.50  pred_elim:                              0
% 7.74/1.50  pred_elim_cl:                           0
% 7.74/1.50  pred_elim_cycles:                       1
% 7.74/1.50  merged_defs:                            12
% 7.74/1.50  merged_defs_ncl:                        0
% 7.74/1.50  bin_hyper_res:                          12
% 7.74/1.50  prep_cycles:                            3
% 7.74/1.50  pred_elim_time:                         0.002
% 7.74/1.50  splitting_time:                         0.
% 7.74/1.50  sem_filter_time:                        0.
% 7.74/1.50  monotx_time:                            0.001
% 7.74/1.50  subtype_inf_time:                       0.
% 7.74/1.50  
% 7.74/1.50  ------ Problem properties
% 7.74/1.50  
% 7.74/1.50  clauses:                                17
% 7.74/1.50  conjectures:                            5
% 7.74/1.50  epr:                                    1
% 7.74/1.50  horn:                                   17
% 7.74/1.50  ground:                                 5
% 7.74/1.50  unary:                                  9
% 7.74/1.50  binary:                                 8
% 7.74/1.50  lits:                                   25
% 7.74/1.50  lits_eq:                                12
% 7.74/1.50  fd_pure:                                0
% 7.74/1.50  fd_pseudo:                              0
% 7.74/1.50  fd_cond:                                0
% 7.74/1.50  fd_pseudo_cond:                         0
% 7.74/1.50  ac_symbols:                             0
% 7.74/1.50  
% 7.74/1.50  ------ Propositional Solver
% 7.74/1.50  
% 7.74/1.50  prop_solver_calls:                      32
% 7.74/1.50  prop_fast_solver_calls:                 493
% 7.74/1.50  smt_solver_calls:                       0
% 7.74/1.50  smt_fast_solver_calls:                  0
% 7.74/1.50  prop_num_of_clauses:                    6962
% 7.74/1.50  prop_preprocess_simplified:             10748
% 7.74/1.50  prop_fo_subsumed:                       4
% 7.74/1.50  prop_solver_time:                       0.
% 7.74/1.50  smt_solver_time:                        0.
% 7.74/1.50  smt_fast_solver_time:                   0.
% 7.74/1.50  prop_fast_solver_time:                  0.
% 7.74/1.50  prop_unsat_core_time:                   0.
% 7.74/1.50  
% 7.74/1.50  ------ QBF
% 7.74/1.50  
% 7.74/1.50  qbf_q_res:                              0
% 7.74/1.50  qbf_num_tautologies:                    0
% 7.74/1.50  qbf_prep_cycles:                        0
% 7.74/1.50  
% 7.74/1.50  ------ BMC1
% 7.74/1.50  
% 7.74/1.50  bmc1_current_bound:                     -1
% 7.74/1.50  bmc1_last_solved_bound:                 -1
% 7.74/1.50  bmc1_unsat_core_size:                   -1
% 7.74/1.50  bmc1_unsat_core_parents_size:           -1
% 7.74/1.50  bmc1_merge_next_fun:                    0
% 7.74/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.50  
% 7.74/1.50  ------ Instantiation
% 7.74/1.50  
% 7.74/1.50  inst_num_of_clauses:                    2375
% 7.74/1.50  inst_num_in_passive:                    1561
% 7.74/1.50  inst_num_in_active:                     776
% 7.74/1.50  inst_num_in_unprocessed:                38
% 7.74/1.50  inst_num_of_loops:                      810
% 7.74/1.50  inst_num_of_learning_restarts:          0
% 7.74/1.50  inst_num_moves_active_passive:          26
% 7.74/1.50  inst_lit_activity:                      0
% 7.74/1.50  inst_lit_activity_moves:                0
% 7.74/1.50  inst_num_tautologies:                   0
% 7.74/1.50  inst_num_prop_implied:                  0
% 7.74/1.50  inst_num_existing_simplified:           0
% 7.74/1.50  inst_num_eq_res_simplified:             0
% 7.74/1.50  inst_num_child_elim:                    0
% 7.74/1.50  inst_num_of_dismatching_blockings:      883
% 7.74/1.50  inst_num_of_non_proper_insts:           2635
% 7.74/1.50  inst_num_of_duplicates:                 0
% 7.74/1.50  inst_inst_num_from_inst_to_res:         0
% 7.74/1.50  inst_dismatching_checking_time:         0.
% 7.74/1.50  
% 7.74/1.50  ------ Resolution
% 7.74/1.50  
% 7.74/1.50  res_num_of_clauses:                     0
% 7.74/1.50  res_num_in_passive:                     0
% 7.74/1.50  res_num_in_active:                      0
% 7.74/1.50  res_num_of_loops:                       71
% 7.74/1.50  res_forward_subset_subsumed:            317
% 7.74/1.50  res_backward_subset_subsumed:           0
% 7.74/1.50  res_forward_subsumed:                   0
% 7.74/1.50  res_backward_subsumed:                  0
% 7.74/1.50  res_forward_subsumption_resolution:     0
% 7.74/1.50  res_backward_subsumption_resolution:    0
% 7.74/1.50  res_clause_to_clause_subsumption:       10522
% 7.74/1.50  res_orphan_elimination:                 0
% 7.74/1.50  res_tautology_del:                      157
% 7.74/1.50  res_num_eq_res_simplified:              0
% 7.74/1.50  res_num_sel_changes:                    0
% 7.74/1.50  res_moves_from_active_to_pass:          0
% 7.74/1.50  
% 7.74/1.50  ------ Superposition
% 7.74/1.50  
% 7.74/1.50  sup_time_total:                         0.
% 7.74/1.50  sup_time_generating:                    0.
% 7.74/1.50  sup_time_sim_full:                      0.
% 7.74/1.50  sup_time_sim_immed:                     0.
% 7.74/1.50  
% 7.74/1.50  sup_num_of_clauses:                     1027
% 7.74/1.50  sup_num_in_active:                      93
% 7.74/1.50  sup_num_in_passive:                     934
% 7.74/1.50  sup_num_of_loops:                       160
% 7.74/1.50  sup_fw_superposition:                   1874
% 7.74/1.50  sup_bw_superposition:                   1606
% 7.74/1.50  sup_immediate_simplified:               2389
% 7.74/1.50  sup_given_eliminated:                   5
% 7.74/1.50  comparisons_done:                       0
% 7.74/1.50  comparisons_avoided:                    0
% 7.74/1.50  
% 7.74/1.50  ------ Simplifications
% 7.74/1.50  
% 7.74/1.50  
% 7.74/1.50  sim_fw_subset_subsumed:                 36
% 7.74/1.50  sim_bw_subset_subsumed:                 0
% 7.74/1.50  sim_fw_subsumed:                        587
% 7.74/1.50  sim_bw_subsumed:                        29
% 7.74/1.50  sim_fw_subsumption_res:                 0
% 7.74/1.50  sim_bw_subsumption_res:                 0
% 7.74/1.50  sim_tautology_del:                      0
% 7.74/1.50  sim_eq_tautology_del:                   619
% 7.74/1.50  sim_eq_res_simp:                        40
% 7.74/1.50  sim_fw_demodulated:                     1403
% 7.74/1.50  sim_bw_demodulated:                     77
% 7.74/1.50  sim_light_normalised:                   930
% 7.74/1.50  sim_joinable_taut:                      0
% 7.74/1.50  sim_joinable_simp:                      0
% 7.74/1.50  sim_ac_normalised:                      0
% 7.74/1.50  sim_smt_subsumption:                    0
% 7.74/1.50  
%------------------------------------------------------------------------------
