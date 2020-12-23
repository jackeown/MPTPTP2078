%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:55 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 253 expanded)
%              Number of clauses        :   62 (  89 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   24
%              Number of atoms          :  319 ( 852 expanded)
%              Number of equality atoms :  127 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK1) != sK2
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( k1_subset_1(sK1) = sK2
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).

fof(f53,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f54,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f39,f37])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1212,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1208,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1208])).

cnf(c_171,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_172,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_378,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_13])).

cnf(c_379,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_389,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_379,c_17])).

cnf(c_392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_3328,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_392])).

cnf(c_3329,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3328])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1217,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1206,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3336,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3329,c_1206])).

cnf(c_3511,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_1217,c_3336])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1216,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1655,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1217,c_1216])).

cnf(c_3521,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3511,c_1655])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3521,c_1205])).

cnf(c_3685,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3329,c_3677])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_67,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3890,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3685,c_67])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1207,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3898,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_1207])).

cnf(c_24,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4283,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_24])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1211,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4290,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_1211])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1202,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1656,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1202,c_1216])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_68,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1355,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1201,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1731,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1201,c_1206])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_290,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | X3 != X2
    | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1200,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_1811,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_1200])).

cnf(c_1823,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(X0,sK2)
    | k1_xboole_0 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1811])).

cnf(c_1825,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_1826,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1656,c_18,c_68,c_1355,c_1825])).

cnf(c_1203,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1831,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1826,c_1203])).

cnf(c_1835,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1831])).

cnf(c_4304,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4290,c_1835])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:47:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.22/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/0.93  
% 2.22/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/0.93  
% 2.22/0.93  ------  iProver source info
% 2.22/0.93  
% 2.22/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.22/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/0.93  git: non_committed_changes: false
% 2.22/0.93  git: last_make_outside_of_git: false
% 2.22/0.93  
% 2.22/0.93  ------ 
% 2.22/0.93  
% 2.22/0.93  ------ Input Options
% 2.22/0.93  
% 2.22/0.93  --out_options                           all
% 2.22/0.93  --tptp_safe_out                         true
% 2.22/0.93  --problem_path                          ""
% 2.22/0.93  --include_path                          ""
% 2.22/0.93  --clausifier                            res/vclausify_rel
% 2.22/0.93  --clausifier_options                    --mode clausify
% 2.22/0.93  --stdin                                 false
% 2.22/0.93  --stats_out                             all
% 2.22/0.93  
% 2.22/0.93  ------ General Options
% 2.22/0.93  
% 2.22/0.93  --fof                                   false
% 2.22/0.93  --time_out_real                         305.
% 2.22/0.93  --time_out_virtual                      -1.
% 2.22/0.93  --symbol_type_check                     false
% 2.22/0.93  --clausify_out                          false
% 2.22/0.93  --sig_cnt_out                           false
% 2.22/0.93  --trig_cnt_out                          false
% 2.22/0.93  --trig_cnt_out_tolerance                1.
% 2.22/0.93  --trig_cnt_out_sk_spl                   false
% 2.22/0.93  --abstr_cl_out                          false
% 2.22/0.93  
% 2.22/0.93  ------ Global Options
% 2.22/0.93  
% 2.22/0.93  --schedule                              default
% 2.22/0.93  --add_important_lit                     false
% 2.22/0.93  --prop_solver_per_cl                    1000
% 2.22/0.93  --min_unsat_core                        false
% 2.22/0.93  --soft_assumptions                      false
% 2.22/0.93  --soft_lemma_size                       3
% 2.22/0.93  --prop_impl_unit_size                   0
% 2.22/0.93  --prop_impl_unit                        []
% 2.22/0.93  --share_sel_clauses                     true
% 2.22/0.93  --reset_solvers                         false
% 2.22/0.93  --bc_imp_inh                            [conj_cone]
% 2.22/0.93  --conj_cone_tolerance                   3.
% 2.22/0.93  --extra_neg_conj                        none
% 2.22/0.93  --large_theory_mode                     true
% 2.22/0.93  --prolific_symb_bound                   200
% 2.22/0.93  --lt_threshold                          2000
% 2.22/0.93  --clause_weak_htbl                      true
% 2.22/0.93  --gc_record_bc_elim                     false
% 2.22/0.93  
% 2.22/0.93  ------ Preprocessing Options
% 2.22/0.93  
% 2.22/0.93  --preprocessing_flag                    true
% 2.22/0.93  --time_out_prep_mult                    0.1
% 2.22/0.93  --splitting_mode                        input
% 2.22/0.93  --splitting_grd                         true
% 2.22/0.93  --splitting_cvd                         false
% 2.22/0.93  --splitting_cvd_svl                     false
% 2.22/0.93  --splitting_nvd                         32
% 2.22/0.93  --sub_typing                            true
% 2.22/0.93  --prep_gs_sim                           true
% 2.22/0.93  --prep_unflatten                        true
% 2.22/0.93  --prep_res_sim                          true
% 2.22/0.93  --prep_upred                            true
% 2.22/0.93  --prep_sem_filter                       exhaustive
% 2.22/0.93  --prep_sem_filter_out                   false
% 2.22/0.93  --pred_elim                             true
% 2.22/0.93  --res_sim_input                         true
% 2.22/0.93  --eq_ax_congr_red                       true
% 2.22/0.93  --pure_diseq_elim                       true
% 2.22/0.93  --brand_transform                       false
% 2.22/0.93  --non_eq_to_eq                          false
% 2.22/0.93  --prep_def_merge                        true
% 2.22/0.93  --prep_def_merge_prop_impl              false
% 2.22/0.93  --prep_def_merge_mbd                    true
% 2.22/0.93  --prep_def_merge_tr_red                 false
% 2.22/0.93  --prep_def_merge_tr_cl                  false
% 2.22/0.93  --smt_preprocessing                     true
% 2.22/0.93  --smt_ac_axioms                         fast
% 2.22/0.93  --preprocessed_out                      false
% 2.22/0.93  --preprocessed_stats                    false
% 2.22/0.93  
% 2.22/0.93  ------ Abstraction refinement Options
% 2.22/0.93  
% 2.22/0.93  --abstr_ref                             []
% 2.22/0.93  --abstr_ref_prep                        false
% 2.22/0.93  --abstr_ref_until_sat                   false
% 2.22/0.93  --abstr_ref_sig_restrict                funpre
% 2.22/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.93  --abstr_ref_under                       []
% 2.22/0.93  
% 2.22/0.93  ------ SAT Options
% 2.22/0.93  
% 2.22/0.93  --sat_mode                              false
% 2.22/0.93  --sat_fm_restart_options                ""
% 2.22/0.93  --sat_gr_def                            false
% 2.22/0.93  --sat_epr_types                         true
% 2.22/0.93  --sat_non_cyclic_types                  false
% 2.22/0.93  --sat_finite_models                     false
% 2.22/0.93  --sat_fm_lemmas                         false
% 2.22/0.93  --sat_fm_prep                           false
% 2.22/0.93  --sat_fm_uc_incr                        true
% 2.22/0.93  --sat_out_model                         small
% 2.22/0.93  --sat_out_clauses                       false
% 2.22/0.93  
% 2.22/0.93  ------ QBF Options
% 2.22/0.93  
% 2.22/0.93  --qbf_mode                              false
% 2.22/0.93  --qbf_elim_univ                         false
% 2.22/0.93  --qbf_dom_inst                          none
% 2.22/0.93  --qbf_dom_pre_inst                      false
% 2.22/0.93  --qbf_sk_in                             false
% 2.22/0.93  --qbf_pred_elim                         true
% 2.22/0.93  --qbf_split                             512
% 2.22/0.93  
% 2.22/0.93  ------ BMC1 Options
% 2.22/0.93  
% 2.22/0.93  --bmc1_incremental                      false
% 2.22/0.93  --bmc1_axioms                           reachable_all
% 2.22/0.93  --bmc1_min_bound                        0
% 2.22/0.93  --bmc1_max_bound                        -1
% 2.22/0.93  --bmc1_max_bound_default                -1
% 2.22/0.93  --bmc1_symbol_reachability              true
% 2.22/0.93  --bmc1_property_lemmas                  false
% 2.22/0.93  --bmc1_k_induction                      false
% 2.22/0.93  --bmc1_non_equiv_states                 false
% 2.22/0.93  --bmc1_deadlock                         false
% 2.22/0.93  --bmc1_ucm                              false
% 2.22/0.93  --bmc1_add_unsat_core                   none
% 2.22/0.93  --bmc1_unsat_core_children              false
% 2.22/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.93  --bmc1_out_stat                         full
% 2.22/0.93  --bmc1_ground_init                      false
% 2.22/0.93  --bmc1_pre_inst_next_state              false
% 2.22/0.93  --bmc1_pre_inst_state                   false
% 2.22/0.93  --bmc1_pre_inst_reach_state             false
% 2.22/0.93  --bmc1_out_unsat_core                   false
% 2.22/0.93  --bmc1_aig_witness_out                  false
% 2.22/0.93  --bmc1_verbose                          false
% 2.22/0.93  --bmc1_dump_clauses_tptp                false
% 2.22/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.93  --bmc1_dump_file                        -
% 2.22/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.93  --bmc1_ucm_extend_mode                  1
% 2.22/0.93  --bmc1_ucm_init_mode                    2
% 2.22/0.93  --bmc1_ucm_cone_mode                    none
% 2.22/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.93  --bmc1_ucm_relax_model                  4
% 2.22/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.93  --bmc1_ucm_layered_model                none
% 2.22/0.93  --bmc1_ucm_max_lemma_size               10
% 2.22/0.93  
% 2.22/0.93  ------ AIG Options
% 2.22/0.93  
% 2.22/0.93  --aig_mode                              false
% 2.22/0.93  
% 2.22/0.93  ------ Instantiation Options
% 2.22/0.93  
% 2.22/0.93  --instantiation_flag                    true
% 2.22/0.93  --inst_sos_flag                         false
% 2.22/0.93  --inst_sos_phase                        true
% 2.22/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.93  --inst_lit_sel_side                     num_symb
% 2.22/0.93  --inst_solver_per_active                1400
% 2.22/0.93  --inst_solver_calls_frac                1.
% 2.22/0.93  --inst_passive_queue_type               priority_queues
% 2.22/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.93  --inst_passive_queues_freq              [25;2]
% 2.22/0.93  --inst_dismatching                      true
% 2.22/0.93  --inst_eager_unprocessed_to_passive     true
% 2.22/0.93  --inst_prop_sim_given                   true
% 2.22/0.93  --inst_prop_sim_new                     false
% 2.22/0.93  --inst_subs_new                         false
% 2.22/0.93  --inst_eq_res_simp                      false
% 2.22/0.93  --inst_subs_given                       false
% 2.22/0.93  --inst_orphan_elimination               true
% 2.22/0.93  --inst_learning_loop_flag               true
% 2.22/0.93  --inst_learning_start                   3000
% 2.22/0.93  --inst_learning_factor                  2
% 2.22/0.93  --inst_start_prop_sim_after_learn       3
% 2.22/0.93  --inst_sel_renew                        solver
% 2.22/0.93  --inst_lit_activity_flag                true
% 2.22/0.93  --inst_restr_to_given                   false
% 2.22/0.93  --inst_activity_threshold               500
% 2.22/0.93  --inst_out_proof                        true
% 2.22/0.93  
% 2.22/0.93  ------ Resolution Options
% 2.22/0.93  
% 2.22/0.93  --resolution_flag                       true
% 2.22/0.93  --res_lit_sel                           adaptive
% 2.22/0.93  --res_lit_sel_side                      none
% 2.22/0.93  --res_ordering                          kbo
% 2.22/0.93  --res_to_prop_solver                    active
% 2.22/0.93  --res_prop_simpl_new                    false
% 2.22/0.93  --res_prop_simpl_given                  true
% 2.22/0.93  --res_passive_queue_type                priority_queues
% 2.22/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.93  --res_passive_queues_freq               [15;5]
% 2.22/0.93  --res_forward_subs                      full
% 2.22/0.93  --res_backward_subs                     full
% 2.22/0.93  --res_forward_subs_resolution           true
% 2.22/0.93  --res_backward_subs_resolution          true
% 2.22/0.93  --res_orphan_elimination                true
% 2.22/0.93  --res_time_limit                        2.
% 2.22/0.93  --res_out_proof                         true
% 2.22/0.93  
% 2.22/0.93  ------ Superposition Options
% 2.22/0.93  
% 2.22/0.93  --superposition_flag                    true
% 2.22/0.93  --sup_passive_queue_type                priority_queues
% 2.22/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.93  --demod_completeness_check              fast
% 2.22/0.93  --demod_use_ground                      true
% 2.22/0.93  --sup_to_prop_solver                    passive
% 2.22/0.93  --sup_prop_simpl_new                    true
% 2.22/0.93  --sup_prop_simpl_given                  true
% 2.22/0.93  --sup_fun_splitting                     false
% 2.22/0.93  --sup_smt_interval                      50000
% 2.22/0.93  
% 2.22/0.93  ------ Superposition Simplification Setup
% 2.22/0.93  
% 2.22/0.93  --sup_indices_passive                   []
% 2.22/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_full_bw                           [BwDemod]
% 2.22/0.93  --sup_immed_triv                        [TrivRules]
% 2.22/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_immed_bw_main                     []
% 2.22/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.93  
% 2.22/0.93  ------ Combination Options
% 2.22/0.93  
% 2.22/0.93  --comb_res_mult                         3
% 2.22/0.93  --comb_sup_mult                         2
% 2.22/0.93  --comb_inst_mult                        10
% 2.22/0.93  
% 2.22/0.93  ------ Debug Options
% 2.22/0.93  
% 2.22/0.93  --dbg_backtrace                         false
% 2.22/0.93  --dbg_dump_prop_clauses                 false
% 2.22/0.93  --dbg_dump_prop_clauses_file            -
% 2.22/0.93  --dbg_out_stat                          false
% 2.22/0.93  ------ Parsing...
% 2.22/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/0.93  
% 2.22/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.22/0.93  
% 2.22/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/0.93  
% 2.22/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/0.93  ------ Proving...
% 2.22/0.93  ------ Problem Properties 
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  clauses                                 19
% 2.22/0.93  conjectures                             3
% 2.22/0.93  EPR                                     6
% 2.22/0.93  Horn                                    15
% 2.22/0.93  unary                                   3
% 2.22/0.93  binary                                  8
% 2.22/0.93  lits                                    43
% 2.22/0.93  lits eq                                 9
% 2.22/0.93  fd_pure                                 0
% 2.22/0.93  fd_pseudo                               0
% 2.22/0.93  fd_cond                                 1
% 2.22/0.93  fd_pseudo_cond                          3
% 2.22/0.93  AC symbols                              0
% 2.22/0.93  
% 2.22/0.93  ------ Schedule dynamic 5 is on 
% 2.22/0.93  
% 2.22/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  ------ 
% 2.22/0.93  Current options:
% 2.22/0.93  ------ 
% 2.22/0.93  
% 2.22/0.93  ------ Input Options
% 2.22/0.93  
% 2.22/0.93  --out_options                           all
% 2.22/0.93  --tptp_safe_out                         true
% 2.22/0.93  --problem_path                          ""
% 2.22/0.93  --include_path                          ""
% 2.22/0.93  --clausifier                            res/vclausify_rel
% 2.22/0.93  --clausifier_options                    --mode clausify
% 2.22/0.93  --stdin                                 false
% 2.22/0.93  --stats_out                             all
% 2.22/0.93  
% 2.22/0.93  ------ General Options
% 2.22/0.93  
% 2.22/0.93  --fof                                   false
% 2.22/0.93  --time_out_real                         305.
% 2.22/0.93  --time_out_virtual                      -1.
% 2.22/0.93  --symbol_type_check                     false
% 2.22/0.93  --clausify_out                          false
% 2.22/0.93  --sig_cnt_out                           false
% 2.22/0.93  --trig_cnt_out                          false
% 2.22/0.93  --trig_cnt_out_tolerance                1.
% 2.22/0.93  --trig_cnt_out_sk_spl                   false
% 2.22/0.93  --abstr_cl_out                          false
% 2.22/0.93  
% 2.22/0.93  ------ Global Options
% 2.22/0.93  
% 2.22/0.93  --schedule                              default
% 2.22/0.93  --add_important_lit                     false
% 2.22/0.93  --prop_solver_per_cl                    1000
% 2.22/0.93  --min_unsat_core                        false
% 2.22/0.93  --soft_assumptions                      false
% 2.22/0.93  --soft_lemma_size                       3
% 2.22/0.93  --prop_impl_unit_size                   0
% 2.22/0.93  --prop_impl_unit                        []
% 2.22/0.93  --share_sel_clauses                     true
% 2.22/0.93  --reset_solvers                         false
% 2.22/0.93  --bc_imp_inh                            [conj_cone]
% 2.22/0.93  --conj_cone_tolerance                   3.
% 2.22/0.93  --extra_neg_conj                        none
% 2.22/0.93  --large_theory_mode                     true
% 2.22/0.93  --prolific_symb_bound                   200
% 2.22/0.93  --lt_threshold                          2000
% 2.22/0.93  --clause_weak_htbl                      true
% 2.22/0.93  --gc_record_bc_elim                     false
% 2.22/0.93  
% 2.22/0.93  ------ Preprocessing Options
% 2.22/0.93  
% 2.22/0.93  --preprocessing_flag                    true
% 2.22/0.93  --time_out_prep_mult                    0.1
% 2.22/0.93  --splitting_mode                        input
% 2.22/0.93  --splitting_grd                         true
% 2.22/0.93  --splitting_cvd                         false
% 2.22/0.93  --splitting_cvd_svl                     false
% 2.22/0.93  --splitting_nvd                         32
% 2.22/0.93  --sub_typing                            true
% 2.22/0.93  --prep_gs_sim                           true
% 2.22/0.93  --prep_unflatten                        true
% 2.22/0.93  --prep_res_sim                          true
% 2.22/0.93  --prep_upred                            true
% 2.22/0.93  --prep_sem_filter                       exhaustive
% 2.22/0.93  --prep_sem_filter_out                   false
% 2.22/0.93  --pred_elim                             true
% 2.22/0.93  --res_sim_input                         true
% 2.22/0.93  --eq_ax_congr_red                       true
% 2.22/0.93  --pure_diseq_elim                       true
% 2.22/0.93  --brand_transform                       false
% 2.22/0.93  --non_eq_to_eq                          false
% 2.22/0.93  --prep_def_merge                        true
% 2.22/0.93  --prep_def_merge_prop_impl              false
% 2.22/0.93  --prep_def_merge_mbd                    true
% 2.22/0.93  --prep_def_merge_tr_red                 false
% 2.22/0.93  --prep_def_merge_tr_cl                  false
% 2.22/0.93  --smt_preprocessing                     true
% 2.22/0.93  --smt_ac_axioms                         fast
% 2.22/0.93  --preprocessed_out                      false
% 2.22/0.93  --preprocessed_stats                    false
% 2.22/0.93  
% 2.22/0.93  ------ Abstraction refinement Options
% 2.22/0.93  
% 2.22/0.93  --abstr_ref                             []
% 2.22/0.93  --abstr_ref_prep                        false
% 2.22/0.93  --abstr_ref_until_sat                   false
% 2.22/0.93  --abstr_ref_sig_restrict                funpre
% 2.22/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.93  --abstr_ref_under                       []
% 2.22/0.93  
% 2.22/0.93  ------ SAT Options
% 2.22/0.93  
% 2.22/0.93  --sat_mode                              false
% 2.22/0.93  --sat_fm_restart_options                ""
% 2.22/0.93  --sat_gr_def                            false
% 2.22/0.93  --sat_epr_types                         true
% 2.22/0.93  --sat_non_cyclic_types                  false
% 2.22/0.93  --sat_finite_models                     false
% 2.22/0.93  --sat_fm_lemmas                         false
% 2.22/0.93  --sat_fm_prep                           false
% 2.22/0.93  --sat_fm_uc_incr                        true
% 2.22/0.93  --sat_out_model                         small
% 2.22/0.93  --sat_out_clauses                       false
% 2.22/0.93  
% 2.22/0.93  ------ QBF Options
% 2.22/0.93  
% 2.22/0.93  --qbf_mode                              false
% 2.22/0.93  --qbf_elim_univ                         false
% 2.22/0.93  --qbf_dom_inst                          none
% 2.22/0.93  --qbf_dom_pre_inst                      false
% 2.22/0.93  --qbf_sk_in                             false
% 2.22/0.93  --qbf_pred_elim                         true
% 2.22/0.93  --qbf_split                             512
% 2.22/0.93  
% 2.22/0.93  ------ BMC1 Options
% 2.22/0.93  
% 2.22/0.93  --bmc1_incremental                      false
% 2.22/0.93  --bmc1_axioms                           reachable_all
% 2.22/0.93  --bmc1_min_bound                        0
% 2.22/0.93  --bmc1_max_bound                        -1
% 2.22/0.93  --bmc1_max_bound_default                -1
% 2.22/0.93  --bmc1_symbol_reachability              true
% 2.22/0.93  --bmc1_property_lemmas                  false
% 2.22/0.93  --bmc1_k_induction                      false
% 2.22/0.93  --bmc1_non_equiv_states                 false
% 2.22/0.93  --bmc1_deadlock                         false
% 2.22/0.93  --bmc1_ucm                              false
% 2.22/0.93  --bmc1_add_unsat_core                   none
% 2.22/0.93  --bmc1_unsat_core_children              false
% 2.22/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.93  --bmc1_out_stat                         full
% 2.22/0.93  --bmc1_ground_init                      false
% 2.22/0.93  --bmc1_pre_inst_next_state              false
% 2.22/0.93  --bmc1_pre_inst_state                   false
% 2.22/0.93  --bmc1_pre_inst_reach_state             false
% 2.22/0.93  --bmc1_out_unsat_core                   false
% 2.22/0.93  --bmc1_aig_witness_out                  false
% 2.22/0.93  --bmc1_verbose                          false
% 2.22/0.93  --bmc1_dump_clauses_tptp                false
% 2.22/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.93  --bmc1_dump_file                        -
% 2.22/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.93  --bmc1_ucm_extend_mode                  1
% 2.22/0.93  --bmc1_ucm_init_mode                    2
% 2.22/0.93  --bmc1_ucm_cone_mode                    none
% 2.22/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.93  --bmc1_ucm_relax_model                  4
% 2.22/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.93  --bmc1_ucm_layered_model                none
% 2.22/0.93  --bmc1_ucm_max_lemma_size               10
% 2.22/0.93  
% 2.22/0.93  ------ AIG Options
% 2.22/0.93  
% 2.22/0.93  --aig_mode                              false
% 2.22/0.93  
% 2.22/0.93  ------ Instantiation Options
% 2.22/0.93  
% 2.22/0.93  --instantiation_flag                    true
% 2.22/0.93  --inst_sos_flag                         false
% 2.22/0.93  --inst_sos_phase                        true
% 2.22/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.93  --inst_lit_sel_side                     none
% 2.22/0.93  --inst_solver_per_active                1400
% 2.22/0.93  --inst_solver_calls_frac                1.
% 2.22/0.93  --inst_passive_queue_type               priority_queues
% 2.22/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.93  --inst_passive_queues_freq              [25;2]
% 2.22/0.93  --inst_dismatching                      true
% 2.22/0.93  --inst_eager_unprocessed_to_passive     true
% 2.22/0.93  --inst_prop_sim_given                   true
% 2.22/0.93  --inst_prop_sim_new                     false
% 2.22/0.93  --inst_subs_new                         false
% 2.22/0.93  --inst_eq_res_simp                      false
% 2.22/0.93  --inst_subs_given                       false
% 2.22/0.93  --inst_orphan_elimination               true
% 2.22/0.93  --inst_learning_loop_flag               true
% 2.22/0.93  --inst_learning_start                   3000
% 2.22/0.93  --inst_learning_factor                  2
% 2.22/0.93  --inst_start_prop_sim_after_learn       3
% 2.22/0.93  --inst_sel_renew                        solver
% 2.22/0.93  --inst_lit_activity_flag                true
% 2.22/0.93  --inst_restr_to_given                   false
% 2.22/0.93  --inst_activity_threshold               500
% 2.22/0.93  --inst_out_proof                        true
% 2.22/0.93  
% 2.22/0.93  ------ Resolution Options
% 2.22/0.93  
% 2.22/0.93  --resolution_flag                       false
% 2.22/0.93  --res_lit_sel                           adaptive
% 2.22/0.93  --res_lit_sel_side                      none
% 2.22/0.93  --res_ordering                          kbo
% 2.22/0.93  --res_to_prop_solver                    active
% 2.22/0.93  --res_prop_simpl_new                    false
% 2.22/0.93  --res_prop_simpl_given                  true
% 2.22/0.93  --res_passive_queue_type                priority_queues
% 2.22/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.93  --res_passive_queues_freq               [15;5]
% 2.22/0.93  --res_forward_subs                      full
% 2.22/0.93  --res_backward_subs                     full
% 2.22/0.93  --res_forward_subs_resolution           true
% 2.22/0.93  --res_backward_subs_resolution          true
% 2.22/0.93  --res_orphan_elimination                true
% 2.22/0.93  --res_time_limit                        2.
% 2.22/0.93  --res_out_proof                         true
% 2.22/0.93  
% 2.22/0.93  ------ Superposition Options
% 2.22/0.93  
% 2.22/0.93  --superposition_flag                    true
% 2.22/0.93  --sup_passive_queue_type                priority_queues
% 2.22/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.93  --demod_completeness_check              fast
% 2.22/0.93  --demod_use_ground                      true
% 2.22/0.93  --sup_to_prop_solver                    passive
% 2.22/0.93  --sup_prop_simpl_new                    true
% 2.22/0.93  --sup_prop_simpl_given                  true
% 2.22/0.93  --sup_fun_splitting                     false
% 2.22/0.93  --sup_smt_interval                      50000
% 2.22/0.93  
% 2.22/0.93  ------ Superposition Simplification Setup
% 2.22/0.93  
% 2.22/0.93  --sup_indices_passive                   []
% 2.22/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_full_bw                           [BwDemod]
% 2.22/0.93  --sup_immed_triv                        [TrivRules]
% 2.22/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_immed_bw_main                     []
% 2.22/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.93  
% 2.22/0.93  ------ Combination Options
% 2.22/0.93  
% 2.22/0.93  --comb_res_mult                         3
% 2.22/0.93  --comb_sup_mult                         2
% 2.22/0.93  --comb_inst_mult                        10
% 2.22/0.93  
% 2.22/0.93  ------ Debug Options
% 2.22/0.93  
% 2.22/0.93  --dbg_backtrace                         false
% 2.22/0.93  --dbg_dump_prop_clauses                 false
% 2.22/0.93  --dbg_dump_prop_clauses_file            -
% 2.22/0.93  --dbg_out_stat                          false
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  ------ Proving...
% 2.22/0.93  
% 2.22/0.93  
% 2.22/0.93  % SZS status Theorem for theBenchmark.p
% 2.22/0.93  
% 2.22/0.93   Resolution empty clause
% 2.22/0.93  
% 2.22/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/0.93  
% 2.22/0.93  fof(f6,axiom,(
% 2.22/0.93    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f23,plain,(
% 2.22/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.22/0.93    inference(nnf_transformation,[],[f6])).
% 2.22/0.93  
% 2.22/0.93  fof(f24,plain,(
% 2.22/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.22/0.93    inference(rectify,[],[f23])).
% 2.22/0.93  
% 2.22/0.93  fof(f25,plain,(
% 2.22/0.93    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.22/0.93    introduced(choice_axiom,[])).
% 2.22/0.93  
% 2.22/0.93  fof(f26,plain,(
% 2.22/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.22/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.22/0.93  
% 2.22/0.93  fof(f41,plain,(
% 2.22/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.22/0.93    inference(cnf_transformation,[],[f26])).
% 2.22/0.93  
% 2.22/0.93  fof(f63,plain,(
% 2.22/0.93    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.22/0.93    inference(equality_resolution,[],[f41])).
% 2.22/0.93  
% 2.22/0.93  fof(f7,axiom,(
% 2.22/0.93    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f16,plain,(
% 2.22/0.93    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.22/0.93    inference(ennf_transformation,[],[f7])).
% 2.22/0.93  
% 2.22/0.93  fof(f27,plain,(
% 2.22/0.93    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.22/0.93    inference(nnf_transformation,[],[f16])).
% 2.22/0.93  
% 2.22/0.93  fof(f45,plain,(
% 2.22/0.93    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/0.93    inference(cnf_transformation,[],[f27])).
% 2.22/0.93  
% 2.22/0.93  fof(f11,axiom,(
% 2.22/0.93    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f51,plain,(
% 2.22/0.93    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.22/0.93    inference(cnf_transformation,[],[f11])).
% 2.22/0.93  
% 2.22/0.93  fof(f1,axiom,(
% 2.22/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f20,plain,(
% 2.22/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.93    inference(nnf_transformation,[],[f1])).
% 2.22/0.93  
% 2.22/0.93  fof(f21,plain,(
% 2.22/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.93    inference(flattening,[],[f20])).
% 2.22/0.93  
% 2.22/0.93  fof(f33,plain,(
% 2.22/0.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/0.93    inference(cnf_transformation,[],[f21])).
% 2.22/0.93  
% 2.22/0.93  fof(f61,plain,(
% 2.22/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.93    inference(equality_resolution,[],[f33])).
% 2.22/0.93  
% 2.22/0.93  fof(f9,axiom,(
% 2.22/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f17,plain,(
% 2.22/0.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.93    inference(ennf_transformation,[],[f9])).
% 2.22/0.93  
% 2.22/0.93  fof(f49,plain,(
% 2.22/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/0.93    inference(cnf_transformation,[],[f17])).
% 2.22/0.93  
% 2.22/0.93  fof(f3,axiom,(
% 2.22/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f37,plain,(
% 2.22/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.22/0.93    inference(cnf_transformation,[],[f3])).
% 2.22/0.93  
% 2.22/0.93  fof(f58,plain,(
% 2.22/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/0.93    inference(definition_unfolding,[],[f49,f37])).
% 2.22/0.93  
% 2.22/0.93  fof(f2,axiom,(
% 2.22/0.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f22,plain,(
% 2.22/0.93    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.22/0.93    inference(nnf_transformation,[],[f2])).
% 2.22/0.93  
% 2.22/0.93  fof(f36,plain,(
% 2.22/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.22/0.93    inference(cnf_transformation,[],[f22])).
% 2.22/0.93  
% 2.22/0.93  fof(f55,plain,(
% 2.22/0.93    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.22/0.93    inference(definition_unfolding,[],[f36,f37])).
% 2.22/0.93  
% 2.22/0.93  fof(f10,axiom,(
% 2.22/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f18,plain,(
% 2.22/0.93    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.93    inference(ennf_transformation,[],[f10])).
% 2.22/0.93  
% 2.22/0.93  fof(f50,plain,(
% 2.22/0.93    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/0.93    inference(cnf_transformation,[],[f18])).
% 2.22/0.93  
% 2.22/0.93  fof(f32,plain,(
% 2.22/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.22/0.93    inference(cnf_transformation,[],[f21])).
% 2.22/0.93  
% 2.22/0.93  fof(f62,plain,(
% 2.22/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.93    inference(equality_resolution,[],[f32])).
% 2.22/0.93  
% 2.22/0.93  fof(f44,plain,(
% 2.22/0.93    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/0.93    inference(cnf_transformation,[],[f27])).
% 2.22/0.93  
% 2.22/0.93  fof(f40,plain,(
% 2.22/0.93    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.22/0.93    inference(cnf_transformation,[],[f26])).
% 2.22/0.93  
% 2.22/0.93  fof(f64,plain,(
% 2.22/0.93    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.22/0.93    inference(equality_resolution,[],[f40])).
% 2.22/0.93  
% 2.22/0.93  fof(f12,conjecture,(
% 2.22/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.22/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.93  
% 2.22/0.93  fof(f13,negated_conjecture,(
% 2.22/0.93    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.22/0.93    inference(negated_conjecture,[],[f12])).
% 2.22/0.93  
% 2.22/0.93  fof(f19,plain,(
% 2.22/0.93    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.93    inference(ennf_transformation,[],[f13])).
% 2.22/0.93  
% 2.22/0.93  fof(f28,plain,(
% 2.22/0.93    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.93    inference(nnf_transformation,[],[f19])).
% 2.22/0.93  
% 2.22/0.93  fof(f29,plain,(
% 2.22/0.93    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.94    inference(flattening,[],[f28])).
% 2.22/0.94  
% 2.22/0.94  fof(f30,plain,(
% 2.22/0.94    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.22/0.94    introduced(choice_axiom,[])).
% 2.22/0.94  
% 2.22/0.94  fof(f31,plain,(
% 2.22/0.94    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.22/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).
% 2.22/0.94  
% 2.22/0.94  fof(f53,plain,(
% 2.22/0.94    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.22/0.94    inference(cnf_transformation,[],[f31])).
% 2.22/0.94  
% 2.22/0.94  fof(f8,axiom,(
% 2.22/0.94    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.22/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.94  
% 2.22/0.94  fof(f48,plain,(
% 2.22/0.94    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.22/0.94    inference(cnf_transformation,[],[f8])).
% 2.22/0.94  
% 2.22/0.94  fof(f60,plain,(
% 2.22/0.94    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.22/0.94    inference(definition_unfolding,[],[f53,f48])).
% 2.22/0.94  
% 2.22/0.94  fof(f54,plain,(
% 2.22/0.94    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.22/0.94    inference(cnf_transformation,[],[f31])).
% 2.22/0.94  
% 2.22/0.94  fof(f59,plain,(
% 2.22/0.94    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.22/0.94    inference(definition_unfolding,[],[f54,f48])).
% 2.22/0.94  
% 2.22/0.94  fof(f35,plain,(
% 2.22/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.22/0.94    inference(cnf_transformation,[],[f22])).
% 2.22/0.94  
% 2.22/0.94  fof(f56,plain,(
% 2.22/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.22/0.94    inference(definition_unfolding,[],[f35,f37])).
% 2.22/0.94  
% 2.22/0.94  fof(f52,plain,(
% 2.22/0.94    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.22/0.94    inference(cnf_transformation,[],[f31])).
% 2.22/0.94  
% 2.22/0.94  fof(f4,axiom,(
% 2.22/0.94    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.22/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.94  
% 2.22/0.94  fof(f14,plain,(
% 2.22/0.94    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.22/0.94    inference(ennf_transformation,[],[f4])).
% 2.22/0.94  
% 2.22/0.94  fof(f15,plain,(
% 2.22/0.94    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.22/0.94    inference(flattening,[],[f14])).
% 2.22/0.94  
% 2.22/0.94  fof(f38,plain,(
% 2.22/0.94    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.22/0.94    inference(cnf_transformation,[],[f15])).
% 2.22/0.94  
% 2.22/0.94  fof(f5,axiom,(
% 2.22/0.94    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.22/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.94  
% 2.22/0.94  fof(f39,plain,(
% 2.22/0.94    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.22/0.94    inference(cnf_transformation,[],[f5])).
% 2.22/0.94  
% 2.22/0.94  fof(f57,plain,(
% 2.22/0.94    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.22/0.94    inference(definition_unfolding,[],[f39,f37])).
% 2.22/0.94  
% 2.22/0.94  cnf(c_9,plain,
% 2.22/0.94      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.22/0.94      inference(cnf_transformation,[],[f63]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1212,plain,
% 2.22/0.94      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_13,plain,
% 2.22/0.94      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.22/0.94      inference(cnf_transformation,[],[f45]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1208,plain,
% 2.22/0.94      ( m1_subset_1(X0,X1) = iProver_top
% 2.22/0.94      | r2_hidden(X0,X1) != iProver_top
% 2.22/0.94      | v1_xboole_0(X1) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_2227,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top
% 2.22/0.94      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1212,c_1208]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_171,plain,
% 2.22/0.94      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.22/0.94      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_172,plain,
% 2.22/0.94      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.22/0.94      inference(renaming,[status(thm)],[c_171]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_378,plain,
% 2.22/0.94      ( m1_subset_1(X0,X1)
% 2.22/0.94      | ~ r1_tarski(X2,X3)
% 2.22/0.94      | v1_xboole_0(X1)
% 2.22/0.94      | X0 != X2
% 2.22/0.94      | k1_zfmisc_1(X3) != X1 ),
% 2.22/0.94      inference(resolution_lifted,[status(thm)],[c_172,c_13]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_379,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.94      | ~ r1_tarski(X0,X1)
% 2.22/0.94      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 2.22/0.94      inference(unflattening,[status(thm)],[c_378]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_17,plain,
% 2.22/0.94      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.22/0.94      inference(cnf_transformation,[],[f51]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_389,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.22/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_379,c_17]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_392,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3328,plain,
% 2.22/0.94      ( r1_tarski(X0,X1) != iProver_top
% 2.22/0.94      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.22/0.94      inference(global_propositional_subsumption,[status(thm)],[c_2227,c_392]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3329,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.22/0.94      inference(renaming,[status(thm)],[c_3328]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f61]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1217,plain,
% 2.22/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_15,plain,
% 2.22/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.94      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.22/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1206,plain,
% 2.22/0.94      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.22/0.94      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3336,plain,
% 2.22/0.94      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.22/0.94      | r1_tarski(X1,X0) != iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_3329,c_1206]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3511,plain,
% 2.22/0.94      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1217,c_3336]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3,plain,
% 2.22/0.94      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.22/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1216,plain,
% 2.22/0.94      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1655,plain,
% 2.22/0.94      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1217,c_1216]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3521,plain,
% 2.22/0.94      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.22/0.94      inference(light_normalisation,[status(thm)],[c_3511,c_1655]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_16,plain,
% 2.22/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.94      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.22/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1205,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.22/0.94      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3677,plain,
% 2.22/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 2.22/0.94      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_3521,c_1205]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3685,plain,
% 2.22/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 2.22/0.94      | r1_tarski(X0,X0) != iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_3329,c_3677]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f62]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_67,plain,
% 2.22/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3890,plain,
% 2.22/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.94      inference(global_propositional_subsumption,[status(thm)],[c_3685,c_67]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_14,plain,
% 2.22/0.94      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.22/0.94      inference(cnf_transformation,[],[f44]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1207,plain,
% 2.22/0.94      ( m1_subset_1(X0,X1) != iProver_top
% 2.22/0.94      | r2_hidden(X0,X1) = iProver_top
% 2.22/0.94      | v1_xboole_0(X1) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_3898,plain,
% 2.22/0.94      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 2.22/0.94      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_3890,c_1207]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_24,plain,
% 2.22/0.94      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_4283,plain,
% 2.22/0.94      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.94      inference(global_propositional_subsumption,[status(thm)],[c_3898,c_24]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_10,plain,
% 2.22/0.94      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.22/0.94      inference(cnf_transformation,[],[f64]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1211,plain,
% 2.22/0.94      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.22/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_4290,plain,
% 2.22/0.94      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_4283,c_1211]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_19,negated_conjecture,
% 2.22/0.94      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 2.22/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1202,plain,
% 2.22/0.94      ( k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1656,plain,
% 2.22/0.94      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) = k1_xboole_0
% 2.22/0.94      | sK2 = k1_xboole_0 ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1202,c_1216]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_18,negated_conjecture,
% 2.22/0.94      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 2.22/0.94      inference(cnf_transformation,[],[f59]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_68,plain,
% 2.22/0.94      ( r1_tarski(sK2,sK2) ),
% 2.22/0.94      inference(instantiation,[status(thm)],[c_2]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_4,plain,
% 2.22/0.94      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.22/0.94      inference(cnf_transformation,[],[f56]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1355,plain,
% 2.22/0.94      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.22/0.94      | k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) != k1_xboole_0 ),
% 2.22/0.94      inference(instantiation,[status(thm)],[c_4]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_20,negated_conjecture,
% 2.22/0.94      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 2.22/0.94      inference(cnf_transformation,[],[f52]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1201,plain,
% 2.22/0.94      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1731,plain,
% 2.22/0.94      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1201,c_1206]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_5,plain,
% 2.22/0.94      ( ~ r1_xboole_0(X0,X1)
% 2.22/0.94      | ~ r1_tarski(X2,X0)
% 2.22/0.94      | ~ r1_tarski(X2,X1)
% 2.22/0.94      | k1_xboole_0 = X2 ),
% 2.22/0.94      inference(cnf_transformation,[],[f38]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_6,plain,
% 2.22/0.94      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 2.22/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_290,plain,
% 2.22/0.94      ( ~ r1_tarski(X0,X1)
% 2.22/0.94      | ~ r1_tarski(X0,X2)
% 2.22/0.94      | X3 != X2
% 2.22/0.94      | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1
% 2.22/0.94      | k1_xboole_0 = X0 ),
% 2.22/0.94      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_291,plain,
% 2.22/0.94      ( ~ r1_tarski(X0,X1)
% 2.22/0.94      | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
% 2.22/0.94      | k1_xboole_0 = X0 ),
% 2.22/0.94      inference(unflattening,[status(thm)],[c_290]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1200,plain,
% 2.22/0.94      ( k1_xboole_0 = X0
% 2.22/0.94      | r1_tarski(X0,X1) != iProver_top
% 2.22/0.94      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1811,plain,
% 2.22/0.94      ( k1_xboole_0 = X0
% 2.22/0.94      | r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
% 2.22/0.94      | r1_tarski(X0,sK2) != iProver_top ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_1731,c_1200]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1823,plain,
% 2.22/0.94      ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
% 2.22/0.94      | ~ r1_tarski(X0,sK2)
% 2.22/0.94      | k1_xboole_0 = X0 ),
% 2.22/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_1811]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1825,plain,
% 2.22/0.94      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.22/0.94      | ~ r1_tarski(sK2,sK2)
% 2.22/0.94      | k1_xboole_0 = sK2 ),
% 2.22/0.94      inference(instantiation,[status(thm)],[c_1823]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1826,plain,
% 2.22/0.94      ( sK2 = k1_xboole_0 ),
% 2.22/0.94      inference(global_propositional_subsumption,
% 2.22/0.94                [status(thm)],
% 2.22/0.94                [c_1656,c_18,c_68,c_1355,c_1825]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1203,plain,
% 2.22/0.94      ( k1_xboole_0 != sK2
% 2.22/0.94      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 2.22/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1831,plain,
% 2.22/0.94      ( k1_xboole_0 != k1_xboole_0
% 2.22/0.94      | r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.22/0.94      inference(demodulation,[status(thm)],[c_1826,c_1203]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_1835,plain,
% 2.22/0.94      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.22/0.94      inference(equality_resolution_simp,[status(thm)],[c_1831]) ).
% 2.22/0.94  
% 2.22/0.94  cnf(c_4304,plain,
% 2.22/0.94      ( $false ),
% 2.22/0.94      inference(superposition,[status(thm)],[c_4290,c_1835]) ).
% 2.22/0.94  
% 2.22/0.94  
% 2.22/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/0.94  
% 2.22/0.94  ------                               Statistics
% 2.22/0.94  
% 2.22/0.94  ------ General
% 2.22/0.94  
% 2.22/0.94  abstr_ref_over_cycles:                  0
% 2.22/0.94  abstr_ref_under_cycles:                 0
% 2.22/0.94  gc_basic_clause_elim:                   0
% 2.22/0.94  forced_gc_time:                         0
% 2.22/0.94  parsing_time:                           0.009
% 2.22/0.94  unif_index_cands_time:                  0.
% 2.22/0.94  unif_index_add_time:                    0.
% 2.22/0.94  orderings_time:                         0.
% 2.22/0.94  out_proof_time:                         0.008
% 2.22/0.94  total_time:                             0.14
% 2.22/0.94  num_of_symbols:                         44
% 2.22/0.94  num_of_terms:                           3375
% 2.22/0.94  
% 2.22/0.94  ------ Preprocessing
% 2.22/0.94  
% 2.22/0.94  num_of_splits:                          0
% 2.22/0.94  num_of_split_atoms:                     0
% 2.22/0.94  num_of_reused_defs:                     0
% 2.22/0.94  num_eq_ax_congr_red:                    16
% 2.22/0.94  num_of_sem_filtered_clauses:            1
% 2.22/0.94  num_of_subtypes:                        0
% 2.22/0.94  monotx_restored_types:                  0
% 2.22/0.94  sat_num_of_epr_types:                   0
% 2.22/0.94  sat_num_of_non_cyclic_types:            0
% 2.22/0.94  sat_guarded_non_collapsed_types:        0
% 2.22/0.94  num_pure_diseq_elim:                    0
% 2.22/0.94  simp_replaced_by:                       0
% 2.22/0.94  res_preprocessed:                       96
% 2.22/0.94  prep_upred:                             0
% 2.22/0.94  prep_unflattend:                        26
% 2.22/0.94  smt_new_axioms:                         0
% 2.22/0.94  pred_elim_cands:                        4
% 2.22/0.94  pred_elim:                              1
% 2.22/0.94  pred_elim_cl:                           1
% 2.22/0.94  pred_elim_cycles:                       3
% 2.22/0.94  merged_defs:                            24
% 2.22/0.94  merged_defs_ncl:                        0
% 2.22/0.94  bin_hyper_res:                          24
% 2.22/0.94  prep_cycles:                            4
% 2.22/0.94  pred_elim_time:                         0.004
% 2.22/0.94  splitting_time:                         0.
% 2.22/0.94  sem_filter_time:                        0.
% 2.22/0.94  monotx_time:                            0.
% 2.22/0.94  subtype_inf_time:                       0.
% 2.22/0.94  
% 2.22/0.94  ------ Problem properties
% 2.22/0.94  
% 2.22/0.94  clauses:                                19
% 2.22/0.94  conjectures:                            3
% 2.22/0.94  epr:                                    6
% 2.22/0.94  horn:                                   15
% 2.22/0.94  ground:                                 3
% 2.22/0.94  unary:                                  3
% 2.22/0.94  binary:                                 8
% 2.22/0.94  lits:                                   43
% 2.22/0.94  lits_eq:                                9
% 2.22/0.94  fd_pure:                                0
% 2.22/0.94  fd_pseudo:                              0
% 2.22/0.94  fd_cond:                                1
% 2.22/0.94  fd_pseudo_cond:                         3
% 2.22/0.94  ac_symbols:                             0
% 2.22/0.94  
% 2.22/0.94  ------ Propositional Solver
% 2.22/0.94  
% 2.22/0.94  prop_solver_calls:                      27
% 2.22/0.94  prop_fast_solver_calls:                 607
% 2.22/0.94  smt_solver_calls:                       0
% 2.22/0.94  smt_fast_solver_calls:                  0
% 2.22/0.94  prop_num_of_clauses:                    1541
% 2.22/0.94  prop_preprocess_simplified:             4962
% 2.22/0.94  prop_fo_subsumed:                       7
% 2.22/0.94  prop_solver_time:                       0.
% 2.22/0.94  smt_solver_time:                        0.
% 2.22/0.94  smt_fast_solver_time:                   0.
% 2.22/0.94  prop_fast_solver_time:                  0.
% 2.22/0.94  prop_unsat_core_time:                   0.
% 2.22/0.94  
% 2.22/0.94  ------ QBF
% 2.22/0.94  
% 2.22/0.94  qbf_q_res:                              0
% 2.22/0.94  qbf_num_tautologies:                    0
% 2.22/0.94  qbf_prep_cycles:                        0
% 2.22/0.94  
% 2.22/0.94  ------ BMC1
% 2.22/0.94  
% 2.22/0.94  bmc1_current_bound:                     -1
% 2.22/0.94  bmc1_last_solved_bound:                 -1
% 2.22/0.94  bmc1_unsat_core_size:                   -1
% 2.22/0.94  bmc1_unsat_core_parents_size:           -1
% 2.22/0.94  bmc1_merge_next_fun:                    0
% 2.22/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.22/0.94  
% 2.22/0.94  ------ Instantiation
% 2.22/0.94  
% 2.22/0.94  inst_num_of_clauses:                    476
% 2.22/0.94  inst_num_in_passive:                    44
% 2.22/0.94  inst_num_in_active:                     213
% 2.22/0.94  inst_num_in_unprocessed:                219
% 2.22/0.94  inst_num_of_loops:                      230
% 2.22/0.94  inst_num_of_learning_restarts:          0
% 2.22/0.94  inst_num_moves_active_passive:          15
% 2.22/0.94  inst_lit_activity:                      0
% 2.22/0.94  inst_lit_activity_moves:                0
% 2.22/0.94  inst_num_tautologies:                   0
% 2.22/0.94  inst_num_prop_implied:                  0
% 2.22/0.94  inst_num_existing_simplified:           0
% 2.22/0.94  inst_num_eq_res_simplified:             0
% 2.22/0.94  inst_num_child_elim:                    0
% 2.22/0.94  inst_num_of_dismatching_blockings:      167
% 2.22/0.94  inst_num_of_non_proper_insts:           498
% 2.22/0.94  inst_num_of_duplicates:                 0
% 2.22/0.94  inst_inst_num_from_inst_to_res:         0
% 2.22/0.94  inst_dismatching_checking_time:         0.
% 2.22/0.94  
% 2.22/0.94  ------ Resolution
% 2.22/0.94  
% 2.22/0.94  res_num_of_clauses:                     0
% 2.22/0.94  res_num_in_passive:                     0
% 2.22/0.94  res_num_in_active:                      0
% 2.22/0.94  res_num_of_loops:                       100
% 2.22/0.94  res_forward_subset_subsumed:            67
% 2.22/0.94  res_backward_subset_subsumed:           2
% 2.22/0.94  res_forward_subsumed:                   0
% 2.22/0.94  res_backward_subsumed:                  0
% 2.22/0.94  res_forward_subsumption_resolution:     2
% 2.22/0.94  res_backward_subsumption_resolution:    0
% 2.22/0.94  res_clause_to_clause_subsumption:       211
% 2.22/0.94  res_orphan_elimination:                 0
% 2.22/0.94  res_tautology_del:                      83
% 2.22/0.94  res_num_eq_res_simplified:              0
% 2.22/0.94  res_num_sel_changes:                    0
% 2.22/0.94  res_moves_from_active_to_pass:          0
% 2.22/0.94  
% 2.22/0.94  ------ Superposition
% 2.22/0.94  
% 2.22/0.94  sup_time_total:                         0.
% 2.22/0.94  sup_time_generating:                    0.
% 2.22/0.94  sup_time_sim_full:                      0.
% 2.22/0.94  sup_time_sim_immed:                     0.
% 2.22/0.94  
% 2.22/0.94  sup_num_of_clauses:                     60
% 2.22/0.94  sup_num_in_active:                      42
% 2.22/0.94  sup_num_in_passive:                     18
% 2.22/0.94  sup_num_of_loops:                       45
% 2.22/0.94  sup_fw_superposition:                   31
% 2.22/0.94  sup_bw_superposition:                   43
% 2.22/0.94  sup_immediate_simplified:               19
% 2.22/0.94  sup_given_eliminated:                   0
% 2.22/0.94  comparisons_done:                       0
% 2.22/0.94  comparisons_avoided:                    0
% 2.22/0.94  
% 2.22/0.94  ------ Simplifications
% 2.22/0.94  
% 2.22/0.94  
% 2.22/0.94  sim_fw_subset_subsumed:                 9
% 2.22/0.94  sim_bw_subset_subsumed:                 0
% 2.22/0.94  sim_fw_subsumed:                        7
% 2.22/0.94  sim_bw_subsumed:                        0
% 2.22/0.94  sim_fw_subsumption_res:                 0
% 2.22/0.94  sim_bw_subsumption_res:                 0
% 2.22/0.94  sim_tautology_del:                      4
% 2.22/0.94  sim_eq_tautology_del:                   3
% 2.22/0.94  sim_eq_res_simp:                        1
% 2.22/0.94  sim_fw_demodulated:                     2
% 2.22/0.94  sim_bw_demodulated:                     4
% 2.22/0.94  sim_light_normalised:                   3
% 2.22/0.94  sim_joinable_taut:                      0
% 2.22/0.94  sim_joinable_simp:                      0
% 2.22/0.94  sim_ac_normalised:                      0
% 2.22/0.94  sim_smt_subsumption:                    0
% 2.22/0.94  
%------------------------------------------------------------------------------
