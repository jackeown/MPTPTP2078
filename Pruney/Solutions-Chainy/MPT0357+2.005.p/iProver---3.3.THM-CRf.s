%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:46 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 182 expanded)
%              Number of clauses        :   46 (  64 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  228 ( 547 expanded)
%              Number of equality atoms :   77 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,sK3),X1)
        & r1_tarski(k3_subset_1(X0,X1),sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,X2),sK2)
          & r1_tarski(k3_subset_1(sK1,sK2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2)
    & r1_tarski(k3_subset_1(sK1,sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f27,f26])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f32,f32])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_815,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_823,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2580,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_823])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_973,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_974,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_2895,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_22,c_34,c_974])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_827,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2900,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_827])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_831,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3004,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_2900,c_831])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6670,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3004,c_1])).

cnf(c_12,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_821,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_844,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_821,c_14])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_822,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1911,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_844,c_822])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_814,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1910,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_814,c_822])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2202,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),k3_subset_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_819])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5999,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),k3_subset_1(sK1,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_21])).

cnf(c_8698,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,X0),sK2) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_5999])).

cnf(c_14686,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK2) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8698,c_844])).

cnf(c_14694,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6670,c_14686])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_816,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2182,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1910,c_816])).

cnf(c_1909,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_815,c_822])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_817,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2044,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1909,c_817])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14694,c_2182,c_2044])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.67/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.00  
% 3.67/1.00  ------  iProver source info
% 3.67/1.00  
% 3.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.00  git: non_committed_changes: false
% 3.67/1.00  git: last_make_outside_of_git: false
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             all
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         305.
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              default
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           true
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             true
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  ------ Parsing...
% 3.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.00  ------ Proving...
% 3.67/1.00  ------ Problem Properties 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  clauses                                 21
% 3.67/1.00  conjectures                             4
% 3.67/1.00  EPR                                     4
% 3.67/1.00  Horn                                    18
% 3.67/1.00  unary                                   9
% 3.67/1.00  binary                                  4
% 3.67/1.00  lits                                    43
% 3.67/1.00  lits eq                                 7
% 3.67/1.00  fd_pure                                 0
% 3.67/1.00  fd_pseudo                               0
% 3.67/1.00  fd_cond                                 0
% 3.67/1.00  fd_pseudo_cond                          2
% 3.67/1.00  AC symbols                              0
% 3.67/1.00  
% 3.67/1.00  ------ Schedule dynamic 5 is on 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  Current options:
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             all
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         305.
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              default
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           true
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             true
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     none
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       false
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ Proving...
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS status Theorem for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  fof(f12,conjecture,(
% 3.67/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f13,negated_conjecture,(
% 3.67/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 3.67/1.00    inference(negated_conjecture,[],[f12])).
% 3.67/1.00  
% 3.67/1.00  fof(f18,plain,(
% 3.67/1.00    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f13])).
% 3.67/1.00  
% 3.67/1.00  fof(f19,plain,(
% 3.67/1.00    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/1.00    inference(flattening,[],[f18])).
% 3.67/1.00  
% 3.67/1.00  fof(f27,plain,(
% 3.67/1.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,sK3),X1) & r1_tarski(k3_subset_1(X0,X1),sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f26,plain,(
% 3.67/1.00    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,X2),sK2) & r1_tarski(k3_subset_1(sK1,sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    (~r1_tarski(k3_subset_1(sK1,sK3),sK2) & r1_tarski(k3_subset_1(sK1,sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f27,f26])).
% 3.67/1.00  
% 3.67/1.00  fof(f48,plain,(
% 3.67/1.00    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.67/1.00    inference(cnf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f6,axiom,(
% 3.67/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f15,plain,(
% 3.67/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f24,plain,(
% 3.67/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.67/1.00    inference(nnf_transformation,[],[f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f37,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f9,axiom,(
% 3.67/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f43,plain,(
% 3.67/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f5,axiom,(
% 3.67/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f20,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f5])).
% 3.67/1.00  
% 3.67/1.00  fof(f21,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/1.00    inference(rectify,[],[f20])).
% 3.67/1.00  
% 3.67/1.00  fof(f22,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f23,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f33,plain,(
% 3.67/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.67/1.00    inference(cnf_transformation,[],[f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f55,plain,(
% 3.67/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.67/1.00    inference(equality_resolution,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f14,plain,(
% 3.67/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.67/1.00    inference(ennf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  fof(f31,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f14])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f32,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f53,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f31,f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f52,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f29,f32,f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f8,axiom,(
% 3.67/1.00    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f42,plain,(
% 3.67/1.00    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f10,axiom,(
% 3.67/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f44,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f7,axiom,(
% 3.67/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f16,plain,(
% 3.67/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f7])).
% 3.67/1.00  
% 3.67/1.00  fof(f41,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f16])).
% 3.67/1.00  
% 3.67/1.00  fof(f47,plain,(
% 3.67/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.67/1.00    inference(cnf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f11,axiom,(
% 3.67/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f17,plain,(
% 3.67/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f25,plain,(
% 3.67/1.00    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/1.00    inference(nnf_transformation,[],[f17])).
% 3.67/1.00  
% 3.67/1.00  fof(f46,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f49,plain,(
% 3.67/1.00    r1_tarski(k3_subset_1(sK1,sK2),sK3)),
% 3.67/1.00    inference(cnf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f50,plain,(
% 3.67/1.00    ~r1_tarski(k3_subset_1(sK1,sK3),sK2)),
% 3.67/1.00    inference(cnf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_19,negated_conjecture,
% 3.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_815,plain,
% 3.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_10,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_823,plain,
% 3.67/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.67/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2580,plain,
% 3.67/1.00      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 3.67/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_815,c_823]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_22,plain,
% 3.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13,plain,
% 3.67/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_32,plain,
% 3.67/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_34,plain,
% 3.67/1.00      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_973,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.67/1.00      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 3.67/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_974,plain,
% 3.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.00      | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 3.67/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2895,plain,
% 3.67/1.00      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_2580,c_22,c_34,c_974]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_827,plain,
% 3.67/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2900,plain,
% 3.67/1.00      ( r1_tarski(sK3,sK1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2895,c_827]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_831,plain,
% 3.67/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.67/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3004,plain,
% 3.67/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2900,c_831]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6670,plain,
% 3.67/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3004,c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12,plain,
% 3.67/1.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_821,plain,
% 3.67/1.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14,plain,
% 3.67/1.00      ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_844,plain,
% 3.67/1.00      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_821,c_14]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/1.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_822,plain,
% 3.67/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.67/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1911,plain,
% 3.67/1.00      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_844,c_822]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_20,negated_conjecture,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_814,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1910,plain,
% 3.67/1.00      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_814,c_822]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.67/1.00      | r1_tarski(X0,X2)
% 3.67/1.00      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_819,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.67/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.67/1.00      | r1_tarski(X0,X2) = iProver_top
% 3.67/1.00      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2202,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.00      | r1_tarski(X0,sK2) = iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,sK2),k3_subset_1(sK1,X0)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1910,c_819]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_21,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5999,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.00      | r1_tarski(X0,sK2) = iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,sK2),k3_subset_1(sK1,X0)) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_2202,c_21]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8698,plain,
% 3.67/1.00      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,X0),sK2) = iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1911,c_5999]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14686,plain,
% 3.67/1.00      ( r1_tarski(k4_xboole_0(sK1,X0),sK2) = iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) != iProver_top ),
% 3.67/1.00      inference(forward_subsumption_resolution,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_8698,c_844]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14694,plain,
% 3.67/1.00      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) != iProver_top
% 3.67/1.00      | r1_tarski(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_6670,c_14686]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_18,negated_conjecture,
% 3.67/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
% 3.67/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_816,plain,
% 3.67/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK3) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2182,plain,
% 3.67/1.00      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_1910,c_816]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1909,plain,
% 3.67/1.00      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_815,c_822]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17,negated_conjecture,
% 3.67/1.00      ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
% 3.67/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_817,plain,
% 3.67/1.00      ( r1_tarski(k3_subset_1(sK1,sK3),sK2) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2044,plain,
% 3.67/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_1909,c_817]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(contradiction,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(minisat,[status(thm)],[c_14694,c_2182,c_2044]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ General
% 3.67/1.00  
% 3.67/1.00  abstr_ref_over_cycles:                  0
% 3.67/1.00  abstr_ref_under_cycles:                 0
% 3.67/1.00  gc_basic_clause_elim:                   0
% 3.67/1.00  forced_gc_time:                         0
% 3.67/1.00  parsing_time:                           0.013
% 3.67/1.00  unif_index_cands_time:                  0.
% 3.67/1.00  unif_index_add_time:                    0.
% 3.67/1.00  orderings_time:                         0.
% 3.67/1.00  out_proof_time:                         0.009
% 3.67/1.00  total_time:                             0.448
% 3.67/1.00  num_of_symbols:                         44
% 3.67/1.00  num_of_terms:                           16692
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing
% 3.67/1.00  
% 3.67/1.00  num_of_splits:                          0
% 3.67/1.00  num_of_split_atoms:                     0
% 3.67/1.00  num_of_reused_defs:                     0
% 3.67/1.00  num_eq_ax_congr_red:                    12
% 3.67/1.00  num_of_sem_filtered_clauses:            1
% 3.67/1.00  num_of_subtypes:                        0
% 3.67/1.00  monotx_restored_types:                  0
% 3.67/1.00  sat_num_of_epr_types:                   0
% 3.67/1.00  sat_num_of_non_cyclic_types:            0
% 3.67/1.00  sat_guarded_non_collapsed_types:        0
% 3.67/1.00  num_pure_diseq_elim:                    0
% 3.67/1.00  simp_replaced_by:                       0
% 3.67/1.00  res_preprocessed:                       84
% 3.67/1.00  prep_upred:                             0
% 3.67/1.00  prep_unflattend:                        12
% 3.67/1.00  smt_new_axioms:                         0
% 3.67/1.00  pred_elim_cands:                        4
% 3.67/1.00  pred_elim:                              0
% 3.67/1.00  pred_elim_cl:                           0
% 3.67/1.00  pred_elim_cycles:                       1
% 3.67/1.00  merged_defs:                            6
% 3.67/1.00  merged_defs_ncl:                        0
% 3.67/1.00  bin_hyper_res:                          6
% 3.67/1.00  prep_cycles:                            3
% 3.67/1.00  pred_elim_time:                         0.002
% 3.67/1.00  splitting_time:                         0.
% 3.67/1.00  sem_filter_time:                        0.
% 3.67/1.00  monotx_time:                            0.
% 3.67/1.00  subtype_inf_time:                       0.
% 3.67/1.00  
% 3.67/1.00  ------ Problem properties
% 3.67/1.00  
% 3.67/1.00  clauses:                                21
% 3.67/1.00  conjectures:                            4
% 3.67/1.00  epr:                                    4
% 3.67/1.00  horn:                                   18
% 3.67/1.00  ground:                                 4
% 3.67/1.00  unary:                                  9
% 3.67/1.00  binary:                                 4
% 3.67/1.00  lits:                                   43
% 3.67/1.00  lits_eq:                                7
% 3.67/1.00  fd_pure:                                0
% 3.67/1.00  fd_pseudo:                              0
% 3.67/1.00  fd_cond:                                0
% 3.67/1.00  fd_pseudo_cond:                         2
% 3.67/1.00  ac_symbols:                             0
% 3.67/1.00  
% 3.67/1.00  ------ Propositional Solver
% 3.67/1.00  
% 3.67/1.00  prop_solver_calls:                      25
% 3.67/1.00  prop_fast_solver_calls:                 683
% 3.67/1.00  smt_solver_calls:                       0
% 3.67/1.00  smt_fast_solver_calls:                  0
% 3.67/1.00  prop_num_of_clauses:                    5513
% 3.67/1.00  prop_preprocess_simplified:             8911
% 3.67/1.00  prop_fo_subsumed:                       19
% 3.67/1.00  prop_solver_time:                       0.
% 3.67/1.00  smt_solver_time:                        0.
% 3.67/1.00  smt_fast_solver_time:                   0.
% 3.67/1.00  prop_fast_solver_time:                  0.
% 3.67/1.00  prop_unsat_core_time:                   0.
% 3.67/1.00  
% 3.67/1.00  ------ QBF
% 3.67/1.00  
% 3.67/1.00  qbf_q_res:                              0
% 3.67/1.00  qbf_num_tautologies:                    0
% 3.67/1.00  qbf_prep_cycles:                        0
% 3.67/1.00  
% 3.67/1.00  ------ BMC1
% 3.67/1.00  
% 3.67/1.00  bmc1_current_bound:                     -1
% 3.67/1.00  bmc1_last_solved_bound:                 -1
% 3.67/1.00  bmc1_unsat_core_size:                   -1
% 3.67/1.00  bmc1_unsat_core_parents_size:           -1
% 3.67/1.00  bmc1_merge_next_fun:                    0
% 3.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation
% 3.67/1.00  
% 3.67/1.00  inst_num_of_clauses:                    1189
% 3.67/1.00  inst_num_in_passive:                    507
% 3.67/1.00  inst_num_in_active:                     612
% 3.67/1.00  inst_num_in_unprocessed:                70
% 3.67/1.00  inst_num_of_loops:                      660
% 3.67/1.00  inst_num_of_learning_restarts:          0
% 3.67/1.00  inst_num_moves_active_passive:          44
% 3.67/1.00  inst_lit_activity:                      0
% 3.67/1.00  inst_lit_activity_moves:                0
% 3.67/1.00  inst_num_tautologies:                   0
% 3.67/1.00  inst_num_prop_implied:                  0
% 3.67/1.00  inst_num_existing_simplified:           0
% 3.67/1.00  inst_num_eq_res_simplified:             0
% 3.67/1.00  inst_num_child_elim:                    0
% 3.67/1.00  inst_num_of_dismatching_blockings:      439
% 3.67/1.00  inst_num_of_non_proper_insts:           1333
% 3.67/1.00  inst_num_of_duplicates:                 0
% 3.67/1.00  inst_inst_num_from_inst_to_res:         0
% 3.67/1.00  inst_dismatching_checking_time:         0.
% 3.67/1.00  
% 3.67/1.00  ------ Resolution
% 3.67/1.00  
% 3.67/1.00  res_num_of_clauses:                     0
% 3.67/1.00  res_num_in_passive:                     0
% 3.67/1.00  res_num_in_active:                      0
% 3.67/1.00  res_num_of_loops:                       87
% 3.67/1.00  res_forward_subset_subsumed:            95
% 3.67/1.00  res_backward_subset_subsumed:           4
% 3.67/1.00  res_forward_subsumed:                   0
% 3.67/1.00  res_backward_subsumed:                  0
% 3.67/1.00  res_forward_subsumption_resolution:     2
% 3.67/1.00  res_backward_subsumption_resolution:    0
% 3.67/1.00  res_clause_to_clause_subsumption:       6710
% 3.67/1.00  res_orphan_elimination:                 0
% 3.67/1.00  res_tautology_del:                      119
% 3.67/1.00  res_num_eq_res_simplified:              0
% 3.67/1.00  res_num_sel_changes:                    0
% 3.67/1.00  res_moves_from_active_to_pass:          0
% 3.67/1.00  
% 3.67/1.00  ------ Superposition
% 3.67/1.00  
% 3.67/1.00  sup_time_total:                         0.
% 3.67/1.00  sup_time_generating:                    0.
% 3.67/1.00  sup_time_sim_full:                      0.
% 3.67/1.00  sup_time_sim_immed:                     0.
% 3.67/1.00  
% 3.67/1.00  sup_num_of_clauses:                     856
% 3.67/1.00  sup_num_in_active:                      108
% 3.67/1.00  sup_num_in_passive:                     748
% 3.67/1.00  sup_num_of_loops:                       131
% 3.67/1.00  sup_fw_superposition:                   721
% 3.67/1.00  sup_bw_superposition:                   1305
% 3.67/1.00  sup_immediate_simplified:               836
% 3.67/1.00  sup_given_eliminated:                   0
% 3.67/1.00  comparisons_done:                       0
% 3.67/1.00  comparisons_avoided:                    0
% 3.67/1.00  
% 3.67/1.00  ------ Simplifications
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  sim_fw_subset_subsumed:                 10
% 3.67/1.00  sim_bw_subset_subsumed:                 0
% 3.67/1.00  sim_fw_subsumed:                        144
% 3.67/1.00  sim_bw_subsumed:                        0
% 3.67/1.00  sim_fw_subsumption_res:                 2
% 3.67/1.00  sim_bw_subsumption_res:                 0
% 3.67/1.00  sim_tautology_del:                      16
% 3.67/1.00  sim_eq_tautology_del:                   71
% 3.67/1.00  sim_eq_res_simp:                        0
% 3.67/1.00  sim_fw_demodulated:                     104
% 3.67/1.00  sim_bw_demodulated:                     81
% 3.67/1.00  sim_light_normalised:                   598
% 3.67/1.00  sim_joinable_taut:                      0
% 3.67/1.00  sim_joinable_simp:                      0
% 3.67/1.00  sim_ac_normalised:                      0
% 3.67/1.00  sim_smt_subsumption:                    0
% 3.67/1.00  
%------------------------------------------------------------------------------
