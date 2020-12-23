%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:51 EST 2020

% Result     : Theorem 15.56s
% Output     : CNFRefutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 367 expanded)
%              Number of clauses        :   60 ( 133 expanded)
%              Number of leaves         :   15 (  71 expanded)
%              Depth                    :   24
%              Number of atoms          :  310 (1185 expanded)
%              Number of equality atoms :  127 ( 339 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK2) != sK3
        | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
      & ( k1_subset_1(sK2) = sK3
        | r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k1_subset_1(sK2) != sK3
      | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
    & ( k1_subset_1(sK2) = sK3
      | r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f32])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f42])).

fof(f57,plain,
    ( k1_subset_1(sK2) = sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,
    ( k1_subset_1(sK2) != sK3
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(definition_unfolding,[],[f58,f53])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_311,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_312,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_318,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_312,c_19])).

cnf(c_51022,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_51027,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_51256,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_51022,c_51027])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_51031,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_51347,plain,
    ( k3_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_51256,c_51031])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_324,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_325,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_51161,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
    inference(equality_resolution,[status(thm)],[c_325])).

cnf(c_51265,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = k3_subset_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_51161])).

cnf(c_52955,plain,
    ( k3_subset_1(sK2,sK3) = k5_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_51347,c_51265])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_51025,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_54661,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k5_xboole_0(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_52955,c_51025])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_51037,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_51036,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_51537,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_51037,c_51036])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_51033,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_57649,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r2_hidden(sK0(X0,X1),X3) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51537,c_51033])).

cnf(c_58128,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X3,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51537,c_57649])).

cnf(c_58448,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51037,c_58128])).

cnf(c_75690,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_54661,c_58448])).

cnf(c_320,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_6029,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6030,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6029])).

cnf(c_76093,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_75690,c_320,c_6030])).

cnf(c_76094,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_76093])).

cnf(c_76099,plain,
    ( k3_xboole_0(sK3,X0) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_76094,c_51031])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_51259,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_51033])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2912,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3367,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2912])).

cnf(c_2910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3096,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2910])).

cnf(c_3408,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3367,c_3096])).

cnf(c_51299,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51259,c_3096,c_3367])).

cnf(c_51442,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51037,c_51299])).

cnf(c_51815,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_51442,c_51031])).

cnf(c_53039,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_51815])).

cnf(c_77970,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_76099,c_53039])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_51026,plain,
    ( k1_xboole_0 != sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_54662,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,k5_xboole_0(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52955,c_51026])).

cnf(c_78443,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_77970,c_54662])).

cnf(c_78463,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_78443])).

cnf(c_78465,plain,
    ( r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_78463,c_9])).

cnf(c_78532,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_78465,c_51442])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:29:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.56/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.56/2.49  
% 15.56/2.49  ------  iProver source info
% 15.56/2.49  
% 15.56/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.56/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.56/2.49  git: non_committed_changes: false
% 15.56/2.49  git: last_make_outside_of_git: false
% 15.56/2.49  
% 15.56/2.49  ------ 
% 15.56/2.49  ------ Parsing...
% 15.56/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  ------ Proving...
% 15.56/2.49  ------ Problem Properties 
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  clauses                                 19
% 15.56/2.49  conjectures                             3
% 15.56/2.49  EPR                                     1
% 15.56/2.49  Horn                                    13
% 15.56/2.49  unary                                   3
% 15.56/2.49  binary                                  9
% 15.56/2.49  lits                                    42
% 15.56/2.49  lits eq                                 10
% 15.56/2.49  fd_pure                                 0
% 15.56/2.49  fd_pseudo                               0
% 15.56/2.49  fd_cond                                 0
% 15.56/2.49  fd_pseudo_cond                          2
% 15.56/2.49  AC symbols                              0
% 15.56/2.49  
% 15.56/2.49  ------ Input Options Time Limit: Unbounded
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.56/2.49  Current options:
% 15.56/2.49  ------ 
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  % SZS status Theorem for theBenchmark.p
% 15.56/2.49  
% 15.56/2.49   Resolution empty clause
% 15.56/2.49  
% 15.56/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  fof(f8,axiom,(
% 15.56/2.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f17,plain,(
% 15.56/2.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 15.56/2.49    inference(ennf_transformation,[],[f8])).
% 15.56/2.49  
% 15.56/2.49  fof(f29,plain,(
% 15.56/2.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 15.56/2.49    inference(nnf_transformation,[],[f17])).
% 15.56/2.49  
% 15.56/2.49  fof(f49,plain,(
% 15.56/2.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.56/2.49    inference(cnf_transformation,[],[f29])).
% 15.56/2.49  
% 15.56/2.49  fof(f12,conjecture,(
% 15.56/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f13,negated_conjecture,(
% 15.56/2.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 15.56/2.49    inference(negated_conjecture,[],[f12])).
% 15.56/2.49  
% 15.56/2.49  fof(f19,plain,(
% 15.56/2.49    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.56/2.49    inference(ennf_transformation,[],[f13])).
% 15.56/2.49  
% 15.56/2.49  fof(f30,plain,(
% 15.56/2.49    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.56/2.49    inference(nnf_transformation,[],[f19])).
% 15.56/2.49  
% 15.56/2.49  fof(f31,plain,(
% 15.56/2.49    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.56/2.49    inference(flattening,[],[f30])).
% 15.56/2.49  
% 15.56/2.49  fof(f32,plain,(
% 15.56/2.49    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))) & (k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 15.56/2.49    introduced(choice_axiom,[])).
% 15.56/2.49  
% 15.56/2.49  fof(f33,plain,(
% 15.56/2.49    (k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))) & (k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 15.56/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f32])).
% 15.56/2.49  
% 15.56/2.49  fof(f56,plain,(
% 15.56/2.49    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 15.56/2.49    inference(cnf_transformation,[],[f33])).
% 15.56/2.49  
% 15.56/2.49  fof(f11,axiom,(
% 15.56/2.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f55,plain,(
% 15.56/2.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 15.56/2.49    inference(cnf_transformation,[],[f11])).
% 15.56/2.49  
% 15.56/2.49  fof(f7,axiom,(
% 15.56/2.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f25,plain,(
% 15.56/2.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.56/2.50    inference(nnf_transformation,[],[f7])).
% 15.56/2.50  
% 15.56/2.50  fof(f26,plain,(
% 15.56/2.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.56/2.50    inference(rectify,[],[f25])).
% 15.56/2.50  
% 15.56/2.50  fof(f27,plain,(
% 15.56/2.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 15.56/2.50    introduced(choice_axiom,[])).
% 15.56/2.50  
% 15.56/2.50  fof(f28,plain,(
% 15.56/2.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.56/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 15.56/2.50  
% 15.56/2.50  fof(f45,plain,(
% 15.56/2.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 15.56/2.50    inference(cnf_transformation,[],[f28])).
% 15.56/2.50  
% 15.56/2.50  fof(f63,plain,(
% 15.56/2.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 15.56/2.50    inference(equality_resolution,[],[f45])).
% 15.56/2.50  
% 15.56/2.50  fof(f5,axiom,(
% 15.56/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f16,plain,(
% 15.56/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.56/2.50    inference(ennf_transformation,[],[f5])).
% 15.56/2.50  
% 15.56/2.50  fof(f43,plain,(
% 15.56/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f16])).
% 15.56/2.50  
% 15.56/2.50  fof(f1,axiom,(
% 15.56/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f34,plain,(
% 15.56/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f1])).
% 15.56/2.50  
% 15.56/2.50  fof(f10,axiom,(
% 15.56/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f18,plain,(
% 15.56/2.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.56/2.50    inference(ennf_transformation,[],[f10])).
% 15.56/2.50  
% 15.56/2.50  fof(f54,plain,(
% 15.56/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.56/2.50    inference(cnf_transformation,[],[f18])).
% 15.56/2.50  
% 15.56/2.50  fof(f4,axiom,(
% 15.56/2.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f42,plain,(
% 15.56/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f4])).
% 15.56/2.50  
% 15.56/2.50  fof(f59,plain,(
% 15.56/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.56/2.50    inference(definition_unfolding,[],[f54,f42])).
% 15.56/2.50  
% 15.56/2.50  fof(f57,plain,(
% 15.56/2.50    k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 15.56/2.50    inference(cnf_transformation,[],[f33])).
% 15.56/2.50  
% 15.56/2.50  fof(f9,axiom,(
% 15.56/2.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f53,plain,(
% 15.56/2.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f9])).
% 15.56/2.50  
% 15.56/2.50  fof(f61,plain,(
% 15.56/2.50    k1_xboole_0 = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 15.56/2.50    inference(definition_unfolding,[],[f57,f53])).
% 15.56/2.50  
% 15.56/2.50  fof(f2,axiom,(
% 15.56/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f14,plain,(
% 15.56/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.56/2.50    inference(ennf_transformation,[],[f2])).
% 15.56/2.50  
% 15.56/2.50  fof(f20,plain,(
% 15.56/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.56/2.50    inference(nnf_transformation,[],[f14])).
% 15.56/2.50  
% 15.56/2.50  fof(f21,plain,(
% 15.56/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.56/2.50    inference(rectify,[],[f20])).
% 15.56/2.50  
% 15.56/2.50  fof(f22,plain,(
% 15.56/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.56/2.50    introduced(choice_axiom,[])).
% 15.56/2.50  
% 15.56/2.50  fof(f23,plain,(
% 15.56/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.56/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 15.56/2.50  
% 15.56/2.50  fof(f36,plain,(
% 15.56/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f23])).
% 15.56/2.50  
% 15.56/2.50  fof(f35,plain,(
% 15.56/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f23])).
% 15.56/2.50  
% 15.56/2.50  fof(f3,axiom,(
% 15.56/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f15,plain,(
% 15.56/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 15.56/2.50    inference(ennf_transformation,[],[f3])).
% 15.56/2.50  
% 15.56/2.50  fof(f24,plain,(
% 15.56/2.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 15.56/2.50    inference(nnf_transformation,[],[f15])).
% 15.56/2.50  
% 15.56/2.50  fof(f39,plain,(
% 15.56/2.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 15.56/2.50    inference(cnf_transformation,[],[f24])).
% 15.56/2.50  
% 15.56/2.50  fof(f6,axiom,(
% 15.56/2.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.56/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.50  
% 15.56/2.50  fof(f44,plain,(
% 15.56/2.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.56/2.50    inference(cnf_transformation,[],[f6])).
% 15.56/2.50  
% 15.56/2.50  fof(f41,plain,(
% 15.56/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 15.56/2.50    inference(cnf_transformation,[],[f24])).
% 15.56/2.50  
% 15.56/2.50  fof(f58,plain,(
% 15.56/2.50    k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 15.56/2.50    inference(cnf_transformation,[],[f33])).
% 15.56/2.50  
% 15.56/2.50  fof(f60,plain,(
% 15.56/2.50    k1_xboole_0 != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 15.56/2.50    inference(definition_unfolding,[],[f58,f53])).
% 15.56/2.50  
% 15.56/2.50  cnf(c_17,plain,
% 15.56/2.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.56/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_22,negated_conjecture,
% 15.56/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 15.56/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_311,plain,
% 15.56/2.50      ( r2_hidden(X0,X1)
% 15.56/2.50      | v1_xboole_0(X1)
% 15.56/2.50      | k1_zfmisc_1(sK2) != X1
% 15.56/2.50      | sK3 != X0 ),
% 15.56/2.50      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_312,plain,
% 15.56/2.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) ),
% 15.56/2.50      inference(unflattening,[status(thm)],[c_311]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_19,negated_conjecture,
% 15.56/2.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 15.56/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_318,plain,
% 15.56/2.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
% 15.56/2.50      inference(forward_subsumption_resolution,[status(thm)],[c_312,c_19]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51022,plain,
% 15.56/2.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_13,plain,
% 15.56/2.50      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.56/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51027,plain,
% 15.56/2.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51256,plain,
% 15.56/2.50      ( r1_tarski(sK3,sK2) = iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51022,c_51027]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_8,plain,
% 15.56/2.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.56/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51031,plain,
% 15.56/2.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51347,plain,
% 15.56/2.50      ( k3_xboole_0(sK3,sK2) = sK3 ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51256,c_51031]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_0,plain,
% 15.56/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.56/2.50      inference(cnf_transformation,[],[f34]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_18,plain,
% 15.56/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.56/2.50      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 15.56/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_324,plain,
% 15.56/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 15.56/2.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 15.56/2.50      | sK3 != X1 ),
% 15.56/2.50      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_325,plain,
% 15.56/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 15.56/2.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
% 15.56/2.50      inference(unflattening,[status(thm)],[c_324]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51161,plain,
% 15.56/2.50      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
% 15.56/2.50      inference(equality_resolution,[status(thm)],[c_325]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51265,plain,
% 15.56/2.50      ( k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = k3_subset_1(sK2,sK3) ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_0,c_51161]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_52955,plain,
% 15.56/2.50      ( k3_subset_1(sK2,sK3) = k5_xboole_0(sK2,sK3) ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_51347,c_51265]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_21,negated_conjecture,
% 15.56/2.50      ( r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 = sK3 ),
% 15.56/2.50      inference(cnf_transformation,[],[f61]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51025,plain,
% 15.56/2.50      ( k1_xboole_0 = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3)) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_54661,plain,
% 15.56/2.50      ( sK3 = k1_xboole_0 | r1_tarski(sK3,k5_xboole_0(sK2,sK3)) = iProver_top ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_52955,c_51025]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_2,plain,
% 15.56/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.56/2.50      inference(cnf_transformation,[],[f36]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51037,plain,
% 15.56/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.56/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_3,plain,
% 15.56/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.56/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51036,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.56/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51537,plain,
% 15.56/2.50      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 15.56/2.50      | r1_tarski(X0,X2) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51037,c_51036]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_6,negated_conjecture,
% 15.56/2.50      ( ~ r2_hidden(X0,X1)
% 15.56/2.50      | ~ r2_hidden(X0,X2)
% 15.56/2.50      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 15.56/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51033,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.56/2.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_57649,plain,
% 15.56/2.50      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 15.56/2.50      | r2_hidden(sK0(X0,X1),X3) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X1) = iProver_top
% 15.56/2.50      | r1_tarski(X0,k5_xboole_0(X2,X3)) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51537,c_51033]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_58128,plain,
% 15.56/2.50      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X3) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X1) = iProver_top
% 15.56/2.50      | r1_tarski(X0,k5_xboole_0(X3,X2)) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51537,c_57649]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_58448,plain,
% 15.56/2.50      ( r1_tarski(X0,X1) != iProver_top
% 15.56/2.50      | r1_tarski(X0,X2) = iProver_top
% 15.56/2.50      | r1_tarski(X0,k5_xboole_0(X1,X0)) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51037,c_58128]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_75690,plain,
% 15.56/2.50      ( sK3 = k1_xboole_0
% 15.56/2.50      | r1_tarski(sK3,X0) = iProver_top
% 15.56/2.50      | r1_tarski(sK3,sK2) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_54661,c_58448]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_320,plain,
% 15.56/2.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_6029,plain,
% 15.56/2.50      ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) | r1_tarski(sK3,sK2) ),
% 15.56/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_6030,plain,
% 15.56/2.50      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 15.56/2.50      | r1_tarski(sK3,sK2) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_6029]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_76093,plain,
% 15.56/2.50      ( r1_tarski(sK3,X0) = iProver_top | sK3 = k1_xboole_0 ),
% 15.56/2.50      inference(global_propositional_subsumption,
% 15.56/2.50                [status(thm)],
% 15.56/2.50                [c_75690,c_320,c_6030]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_76094,plain,
% 15.56/2.50      ( sK3 = k1_xboole_0 | r1_tarski(sK3,X0) = iProver_top ),
% 15.56/2.50      inference(renaming,[status(thm)],[c_76093]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_76099,plain,
% 15.56/2.50      ( k3_xboole_0(sK3,X0) = sK3 | sK3 = k1_xboole_0 ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_76094,c_51031]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_9,plain,
% 15.56/2.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.56/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51259,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_9,c_51033]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_4,plain,
% 15.56/2.50      ( ~ r2_hidden(X0,X1)
% 15.56/2.50      | r2_hidden(X0,X2)
% 15.56/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 15.56/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_2912,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.56/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_3367,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.56/2.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_9,c_2912]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_2910,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.56/2.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_3096,plain,
% 15.56/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.56/2.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_9,c_2910]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_3408,plain,
% 15.56/2.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.56/2.50      inference(global_propositional_subsumption,[status(thm)],[c_3367,c_3096]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51299,plain,
% 15.56/2.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.56/2.50      inference(global_propositional_subsumption,
% 15.56/2.50                [status(thm)],
% 15.56/2.50                [c_51259,c_3096,c_3367]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51442,plain,
% 15.56/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51037,c_51299]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51815,plain,
% 15.56/2.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_51442,c_51031]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_53039,plain,
% 15.56/2.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_0,c_51815]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_77970,plain,
% 15.56/2.50      ( sK3 = k1_xboole_0 ),
% 15.56/2.50      inference(superposition,[status(thm)],[c_76099,c_53039]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_20,negated_conjecture,
% 15.56/2.50      ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 != sK3 ),
% 15.56/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_51026,plain,
% 15.56/2.50      ( k1_xboole_0 != sK3
% 15.56/2.50      | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
% 15.56/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_54662,plain,
% 15.56/2.50      ( sK3 != k1_xboole_0
% 15.56/2.50      | r1_tarski(sK3,k5_xboole_0(sK2,sK3)) != iProver_top ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_52955,c_51026]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_78443,plain,
% 15.56/2.50      ( k1_xboole_0 != k1_xboole_0
% 15.56/2.50      | r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_77970,c_54662]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_78463,plain,
% 15.56/2.50      ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 15.56/2.50      inference(equality_resolution_simp,[status(thm)],[c_78443]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_78465,plain,
% 15.56/2.50      ( r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 15.56/2.50      inference(demodulation,[status(thm)],[c_78463,c_9]) ).
% 15.56/2.50  
% 15.56/2.50  cnf(c_78532,plain,
% 15.56/2.50      ( $false ),
% 15.56/2.50      inference(forward_subsumption_resolution,[status(thm)],[c_78465,c_51442]) ).
% 15.56/2.50  
% 15.56/2.50  
% 15.56/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.56/2.50  
% 15.56/2.50  ------                               Statistics
% 15.56/2.50  
% 15.56/2.50  ------ Selected
% 15.56/2.50  
% 15.56/2.50  total_time:                             1.911
% 15.56/2.50  
%------------------------------------------------------------------------------
