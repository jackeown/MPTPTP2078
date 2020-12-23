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
% DateTime   : Thu Dec  3 11:40:07 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 402 expanded)
%              Number of clauses        :  101 ( 168 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  395 (1394 expanded)
%              Number of equality atoms :  191 ( 466 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK1) != sK2
        | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & ( k2_subset_1(sK1) = sK2
        | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

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

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4004,plain,
    ( r1_tarski(sK1,X0)
    | k4_xboole_0(sK1,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4006,plain,
    ( r1_tarski(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4004])).

cnf(c_730,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1622,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_3944,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3945,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3944])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1256,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2117,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1250,c_1256])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1251,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1281,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1251,c_15])).

cnf(c_2282,plain,
    ( sK2 = sK1
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2117,c_1281])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2300,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2117,c_1255])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2687,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_23])).

cnf(c_2694,plain,
    ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2687,c_1256])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1253,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2046,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1250,c_1253])).

cnf(c_2280,plain,
    ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2117,c_2046])).

cnf(c_2699,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2694,c_2280])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1265,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3288,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2699,c_1265])).

cnf(c_3691,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_2282,c_3288])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1257,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2061,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1257])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1442,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_18,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1496,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1497,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_2434,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2061,c_23,c_1442,c_1497])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1261,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2439,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_1261])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1270,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2829,plain,
    ( sK2 = sK1
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_1270])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_34,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_69,plain,
    ( k4_xboole_0(sK2,sK2) != k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_74,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_184,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_373,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_13])).

cnf(c_374,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_375,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_732,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_739,plain,
    ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1252,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1306,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1252,c_15])).

cnf(c_1616,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1617,plain,
    ( sK1 = X0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_1619,plain,
    ( sK1 = sK2
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1617])).

cnf(c_1900,plain,
    ( ~ r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1904,plain,
    ( r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_737,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1993,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1998,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK2,sK2)
    | sK2 != sK2
    | sK1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_2220,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(sK1))
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2226,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_2228,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_1716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2343,plain,
    ( ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
    | r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_2344,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1467,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))
    | X0 != k3_subset_1(X2,X3)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1863,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | X0 != k3_subset_1(X1,X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_2862,plain,
    ( ~ m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2))
    | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,X0)
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2869,plain,
    ( k3_subset_1(sK1,sK2) != k3_subset_1(sK2,X0)
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
    | m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_2871,plain,
    ( k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
    | m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_3163,plain,
    ( r1_tarski(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_23,c_31,c_34,c_69,c_71,c_74,c_78,c_377,c_739,c_1306,c_1442,c_1497,c_1619,c_1904,c_1998,c_2228,c_2344,c_2871])).

cnf(c_3165,plain,
    ( ~ r1_tarski(sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3163])).

cnf(c_2870,plain,
    ( ~ m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2))
    | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_729,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2213,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1375,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1306])).

cnf(c_376,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ r1_tarski(sK2,sK2)
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_33,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4006,c_3945,c_3691,c_3165,c_2870,c_2343,c_2213,c_1998,c_1900,c_1375,c_739,c_376,c_78,c_74,c_33,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.29/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.01  
% 2.29/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.29/1.01  
% 2.29/1.01  ------  iProver source info
% 2.29/1.01  
% 2.29/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.29/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.29/1.01  git: non_committed_changes: false
% 2.29/1.01  git: last_make_outside_of_git: false
% 2.29/1.01  
% 2.29/1.01  ------ 
% 2.29/1.01  
% 2.29/1.01  ------ Input Options
% 2.29/1.01  
% 2.29/1.01  --out_options                           all
% 2.29/1.01  --tptp_safe_out                         true
% 2.29/1.01  --problem_path                          ""
% 2.29/1.01  --include_path                          ""
% 2.29/1.01  --clausifier                            res/vclausify_rel
% 2.29/1.01  --clausifier_options                    --mode clausify
% 2.29/1.01  --stdin                                 false
% 2.29/1.01  --stats_out                             all
% 2.29/1.01  
% 2.29/1.01  ------ General Options
% 2.29/1.01  
% 2.29/1.01  --fof                                   false
% 2.29/1.01  --time_out_real                         305.
% 2.29/1.01  --time_out_virtual                      -1.
% 2.29/1.01  --symbol_type_check                     false
% 2.29/1.01  --clausify_out                          false
% 2.29/1.01  --sig_cnt_out                           false
% 2.29/1.01  --trig_cnt_out                          false
% 2.29/1.01  --trig_cnt_out_tolerance                1.
% 2.29/1.01  --trig_cnt_out_sk_spl                   false
% 2.29/1.01  --abstr_cl_out                          false
% 2.29/1.01  
% 2.29/1.01  ------ Global Options
% 2.29/1.01  
% 2.29/1.01  --schedule                              default
% 2.29/1.01  --add_important_lit                     false
% 2.29/1.01  --prop_solver_per_cl                    1000
% 2.29/1.01  --min_unsat_core                        false
% 2.29/1.01  --soft_assumptions                      false
% 2.29/1.01  --soft_lemma_size                       3
% 2.29/1.01  --prop_impl_unit_size                   0
% 2.29/1.01  --prop_impl_unit                        []
% 2.29/1.01  --share_sel_clauses                     true
% 2.29/1.01  --reset_solvers                         false
% 2.29/1.01  --bc_imp_inh                            [conj_cone]
% 2.29/1.01  --conj_cone_tolerance                   3.
% 2.29/1.01  --extra_neg_conj                        none
% 2.29/1.01  --large_theory_mode                     true
% 2.29/1.01  --prolific_symb_bound                   200
% 2.29/1.01  --lt_threshold                          2000
% 2.29/1.01  --clause_weak_htbl                      true
% 2.29/1.01  --gc_record_bc_elim                     false
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing Options
% 2.29/1.01  
% 2.29/1.01  --preprocessing_flag                    true
% 2.29/1.01  --time_out_prep_mult                    0.1
% 2.29/1.01  --splitting_mode                        input
% 2.29/1.01  --splitting_grd                         true
% 2.29/1.01  --splitting_cvd                         false
% 2.29/1.01  --splitting_cvd_svl                     false
% 2.29/1.01  --splitting_nvd                         32
% 2.29/1.01  --sub_typing                            true
% 2.29/1.01  --prep_gs_sim                           true
% 2.29/1.01  --prep_unflatten                        true
% 2.29/1.01  --prep_res_sim                          true
% 2.29/1.01  --prep_upred                            true
% 2.29/1.01  --prep_sem_filter                       exhaustive
% 2.29/1.01  --prep_sem_filter_out                   false
% 2.29/1.01  --pred_elim                             true
% 2.29/1.01  --res_sim_input                         true
% 2.29/1.01  --eq_ax_congr_red                       true
% 2.29/1.01  --pure_diseq_elim                       true
% 2.29/1.01  --brand_transform                       false
% 2.29/1.01  --non_eq_to_eq                          false
% 2.29/1.01  --prep_def_merge                        true
% 2.29/1.01  --prep_def_merge_prop_impl              false
% 2.29/1.01  --prep_def_merge_mbd                    true
% 2.29/1.01  --prep_def_merge_tr_red                 false
% 2.29/1.01  --prep_def_merge_tr_cl                  false
% 2.29/1.01  --smt_preprocessing                     true
% 2.29/1.01  --smt_ac_axioms                         fast
% 2.29/1.01  --preprocessed_out                      false
% 2.29/1.01  --preprocessed_stats                    false
% 2.29/1.01  
% 2.29/1.01  ------ Abstraction refinement Options
% 2.29/1.01  
% 2.29/1.01  --abstr_ref                             []
% 2.29/1.01  --abstr_ref_prep                        false
% 2.29/1.01  --abstr_ref_until_sat                   false
% 2.29/1.01  --abstr_ref_sig_restrict                funpre
% 2.29/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.01  --abstr_ref_under                       []
% 2.29/1.01  
% 2.29/1.01  ------ SAT Options
% 2.29/1.01  
% 2.29/1.01  --sat_mode                              false
% 2.29/1.01  --sat_fm_restart_options                ""
% 2.29/1.01  --sat_gr_def                            false
% 2.29/1.01  --sat_epr_types                         true
% 2.29/1.01  --sat_non_cyclic_types                  false
% 2.29/1.01  --sat_finite_models                     false
% 2.29/1.01  --sat_fm_lemmas                         false
% 2.29/1.01  --sat_fm_prep                           false
% 2.29/1.01  --sat_fm_uc_incr                        true
% 2.29/1.01  --sat_out_model                         small
% 2.29/1.01  --sat_out_clauses                       false
% 2.29/1.01  
% 2.29/1.01  ------ QBF Options
% 2.29/1.01  
% 2.29/1.01  --qbf_mode                              false
% 2.29/1.01  --qbf_elim_univ                         false
% 2.29/1.01  --qbf_dom_inst                          none
% 2.29/1.01  --qbf_dom_pre_inst                      false
% 2.29/1.01  --qbf_sk_in                             false
% 2.29/1.01  --qbf_pred_elim                         true
% 2.29/1.01  --qbf_split                             512
% 2.29/1.01  
% 2.29/1.01  ------ BMC1 Options
% 2.29/1.01  
% 2.29/1.01  --bmc1_incremental                      false
% 2.29/1.01  --bmc1_axioms                           reachable_all
% 2.29/1.01  --bmc1_min_bound                        0
% 2.29/1.01  --bmc1_max_bound                        -1
% 2.29/1.01  --bmc1_max_bound_default                -1
% 2.29/1.01  --bmc1_symbol_reachability              true
% 2.29/1.01  --bmc1_property_lemmas                  false
% 2.29/1.01  --bmc1_k_induction                      false
% 2.29/1.01  --bmc1_non_equiv_states                 false
% 2.29/1.01  --bmc1_deadlock                         false
% 2.29/1.01  --bmc1_ucm                              false
% 2.29/1.01  --bmc1_add_unsat_core                   none
% 2.29/1.01  --bmc1_unsat_core_children              false
% 2.29/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.01  --bmc1_out_stat                         full
% 2.29/1.01  --bmc1_ground_init                      false
% 2.29/1.01  --bmc1_pre_inst_next_state              false
% 2.29/1.01  --bmc1_pre_inst_state                   false
% 2.29/1.01  --bmc1_pre_inst_reach_state             false
% 2.29/1.01  --bmc1_out_unsat_core                   false
% 2.29/1.01  --bmc1_aig_witness_out                  false
% 2.29/1.01  --bmc1_verbose                          false
% 2.29/1.01  --bmc1_dump_clauses_tptp                false
% 2.29/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.01  --bmc1_dump_file                        -
% 2.29/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.01  --bmc1_ucm_extend_mode                  1
% 2.29/1.01  --bmc1_ucm_init_mode                    2
% 2.29/1.01  --bmc1_ucm_cone_mode                    none
% 2.29/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.01  --bmc1_ucm_relax_model                  4
% 2.29/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.01  --bmc1_ucm_layered_model                none
% 2.29/1.01  --bmc1_ucm_max_lemma_size               10
% 2.29/1.01  
% 2.29/1.01  ------ AIG Options
% 2.29/1.01  
% 2.29/1.01  --aig_mode                              false
% 2.29/1.01  
% 2.29/1.01  ------ Instantiation Options
% 2.29/1.01  
% 2.29/1.01  --instantiation_flag                    true
% 2.29/1.01  --inst_sos_flag                         false
% 2.29/1.01  --inst_sos_phase                        true
% 2.29/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.01  --inst_lit_sel_side                     num_symb
% 2.29/1.01  --inst_solver_per_active                1400
% 2.29/1.01  --inst_solver_calls_frac                1.
% 2.29/1.01  --inst_passive_queue_type               priority_queues
% 2.29/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.01  --inst_passive_queues_freq              [25;2]
% 2.29/1.01  --inst_dismatching                      true
% 2.29/1.01  --inst_eager_unprocessed_to_passive     true
% 2.29/1.01  --inst_prop_sim_given                   true
% 2.29/1.01  --inst_prop_sim_new                     false
% 2.29/1.01  --inst_subs_new                         false
% 2.29/1.01  --inst_eq_res_simp                      false
% 2.29/1.01  --inst_subs_given                       false
% 2.29/1.01  --inst_orphan_elimination               true
% 2.29/1.01  --inst_learning_loop_flag               true
% 2.29/1.01  --inst_learning_start                   3000
% 2.29/1.01  --inst_learning_factor                  2
% 2.29/1.01  --inst_start_prop_sim_after_learn       3
% 2.29/1.01  --inst_sel_renew                        solver
% 2.29/1.01  --inst_lit_activity_flag                true
% 2.29/1.01  --inst_restr_to_given                   false
% 2.29/1.01  --inst_activity_threshold               500
% 2.29/1.01  --inst_out_proof                        true
% 2.29/1.01  
% 2.29/1.01  ------ Resolution Options
% 2.29/1.01  
% 2.29/1.01  --resolution_flag                       true
% 2.29/1.01  --res_lit_sel                           adaptive
% 2.29/1.01  --res_lit_sel_side                      none
% 2.29/1.01  --res_ordering                          kbo
% 2.29/1.01  --res_to_prop_solver                    active
% 2.29/1.01  --res_prop_simpl_new                    false
% 2.29/1.01  --res_prop_simpl_given                  true
% 2.29/1.01  --res_passive_queue_type                priority_queues
% 2.29/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.01  --res_passive_queues_freq               [15;5]
% 2.29/1.01  --res_forward_subs                      full
% 2.29/1.01  --res_backward_subs                     full
% 2.29/1.01  --res_forward_subs_resolution           true
% 2.29/1.01  --res_backward_subs_resolution          true
% 2.29/1.01  --res_orphan_elimination                true
% 2.29/1.01  --res_time_limit                        2.
% 2.29/1.01  --res_out_proof                         true
% 2.29/1.01  
% 2.29/1.01  ------ Superposition Options
% 2.29/1.01  
% 2.29/1.01  --superposition_flag                    true
% 2.29/1.01  --sup_passive_queue_type                priority_queues
% 2.29/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.01  --demod_completeness_check              fast
% 2.29/1.01  --demod_use_ground                      true
% 2.29/1.01  --sup_to_prop_solver                    passive
% 2.29/1.01  --sup_prop_simpl_new                    true
% 2.29/1.01  --sup_prop_simpl_given                  true
% 2.29/1.01  --sup_fun_splitting                     false
% 2.29/1.01  --sup_smt_interval                      50000
% 2.29/1.01  
% 2.29/1.01  ------ Superposition Simplification Setup
% 2.29/1.01  
% 2.29/1.01  --sup_indices_passive                   []
% 2.29/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_full_bw                           [BwDemod]
% 2.29/1.01  --sup_immed_triv                        [TrivRules]
% 2.29/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_immed_bw_main                     []
% 2.29/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.01  
% 2.29/1.01  ------ Combination Options
% 2.29/1.01  
% 2.29/1.01  --comb_res_mult                         3
% 2.29/1.01  --comb_sup_mult                         2
% 2.29/1.01  --comb_inst_mult                        10
% 2.29/1.01  
% 2.29/1.01  ------ Debug Options
% 2.29/1.01  
% 2.29/1.01  --dbg_backtrace                         false
% 2.29/1.01  --dbg_dump_prop_clauses                 false
% 2.29/1.01  --dbg_dump_prop_clauses_file            -
% 2.29/1.01  --dbg_out_stat                          false
% 2.29/1.01  ------ Parsing...
% 2.29/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.29/1.01  ------ Proving...
% 2.29/1.01  ------ Problem Properties 
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  clauses                                 22
% 2.29/1.01  conjectures                             3
% 2.29/1.01  EPR                                     7
% 2.29/1.01  Horn                                    18
% 2.29/1.01  unary                                   5
% 2.29/1.01  binary                                  10
% 2.29/1.01  lits                                    46
% 2.29/1.01  lits eq                                 11
% 2.29/1.01  fd_pure                                 0
% 2.29/1.01  fd_pseudo                               0
% 2.29/1.01  fd_cond                                 1
% 2.29/1.01  fd_pseudo_cond                          3
% 2.29/1.01  AC symbols                              0
% 2.29/1.01  
% 2.29/1.01  ------ Schedule dynamic 5 is on 
% 2.29/1.01  
% 2.29/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  ------ 
% 2.29/1.01  Current options:
% 2.29/1.01  ------ 
% 2.29/1.01  
% 2.29/1.01  ------ Input Options
% 2.29/1.01  
% 2.29/1.01  --out_options                           all
% 2.29/1.01  --tptp_safe_out                         true
% 2.29/1.01  --problem_path                          ""
% 2.29/1.01  --include_path                          ""
% 2.29/1.01  --clausifier                            res/vclausify_rel
% 2.29/1.01  --clausifier_options                    --mode clausify
% 2.29/1.01  --stdin                                 false
% 2.29/1.01  --stats_out                             all
% 2.29/1.01  
% 2.29/1.01  ------ General Options
% 2.29/1.01  
% 2.29/1.01  --fof                                   false
% 2.29/1.01  --time_out_real                         305.
% 2.29/1.01  --time_out_virtual                      -1.
% 2.29/1.01  --symbol_type_check                     false
% 2.29/1.01  --clausify_out                          false
% 2.29/1.01  --sig_cnt_out                           false
% 2.29/1.01  --trig_cnt_out                          false
% 2.29/1.01  --trig_cnt_out_tolerance                1.
% 2.29/1.01  --trig_cnt_out_sk_spl                   false
% 2.29/1.01  --abstr_cl_out                          false
% 2.29/1.01  
% 2.29/1.01  ------ Global Options
% 2.29/1.01  
% 2.29/1.01  --schedule                              default
% 2.29/1.01  --add_important_lit                     false
% 2.29/1.01  --prop_solver_per_cl                    1000
% 2.29/1.01  --min_unsat_core                        false
% 2.29/1.01  --soft_assumptions                      false
% 2.29/1.01  --soft_lemma_size                       3
% 2.29/1.01  --prop_impl_unit_size                   0
% 2.29/1.01  --prop_impl_unit                        []
% 2.29/1.01  --share_sel_clauses                     true
% 2.29/1.01  --reset_solvers                         false
% 2.29/1.01  --bc_imp_inh                            [conj_cone]
% 2.29/1.01  --conj_cone_tolerance                   3.
% 2.29/1.01  --extra_neg_conj                        none
% 2.29/1.01  --large_theory_mode                     true
% 2.29/1.01  --prolific_symb_bound                   200
% 2.29/1.01  --lt_threshold                          2000
% 2.29/1.01  --clause_weak_htbl                      true
% 2.29/1.01  --gc_record_bc_elim                     false
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing Options
% 2.29/1.01  
% 2.29/1.01  --preprocessing_flag                    true
% 2.29/1.01  --time_out_prep_mult                    0.1
% 2.29/1.01  --splitting_mode                        input
% 2.29/1.01  --splitting_grd                         true
% 2.29/1.01  --splitting_cvd                         false
% 2.29/1.01  --splitting_cvd_svl                     false
% 2.29/1.01  --splitting_nvd                         32
% 2.29/1.01  --sub_typing                            true
% 2.29/1.01  --prep_gs_sim                           true
% 2.29/1.01  --prep_unflatten                        true
% 2.29/1.01  --prep_res_sim                          true
% 2.29/1.01  --prep_upred                            true
% 2.29/1.01  --prep_sem_filter                       exhaustive
% 2.29/1.01  --prep_sem_filter_out                   false
% 2.29/1.01  --pred_elim                             true
% 2.29/1.01  --res_sim_input                         true
% 2.29/1.01  --eq_ax_congr_red                       true
% 2.29/1.01  --pure_diseq_elim                       true
% 2.29/1.01  --brand_transform                       false
% 2.29/1.01  --non_eq_to_eq                          false
% 2.29/1.01  --prep_def_merge                        true
% 2.29/1.01  --prep_def_merge_prop_impl              false
% 2.29/1.01  --prep_def_merge_mbd                    true
% 2.29/1.01  --prep_def_merge_tr_red                 false
% 2.29/1.01  --prep_def_merge_tr_cl                  false
% 2.29/1.01  --smt_preprocessing                     true
% 2.29/1.01  --smt_ac_axioms                         fast
% 2.29/1.01  --preprocessed_out                      false
% 2.29/1.01  --preprocessed_stats                    false
% 2.29/1.01  
% 2.29/1.01  ------ Abstraction refinement Options
% 2.29/1.01  
% 2.29/1.01  --abstr_ref                             []
% 2.29/1.01  --abstr_ref_prep                        false
% 2.29/1.01  --abstr_ref_until_sat                   false
% 2.29/1.01  --abstr_ref_sig_restrict                funpre
% 2.29/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.01  --abstr_ref_under                       []
% 2.29/1.01  
% 2.29/1.01  ------ SAT Options
% 2.29/1.01  
% 2.29/1.01  --sat_mode                              false
% 2.29/1.01  --sat_fm_restart_options                ""
% 2.29/1.01  --sat_gr_def                            false
% 2.29/1.01  --sat_epr_types                         true
% 2.29/1.01  --sat_non_cyclic_types                  false
% 2.29/1.01  --sat_finite_models                     false
% 2.29/1.01  --sat_fm_lemmas                         false
% 2.29/1.01  --sat_fm_prep                           false
% 2.29/1.01  --sat_fm_uc_incr                        true
% 2.29/1.01  --sat_out_model                         small
% 2.29/1.01  --sat_out_clauses                       false
% 2.29/1.01  
% 2.29/1.01  ------ QBF Options
% 2.29/1.01  
% 2.29/1.01  --qbf_mode                              false
% 2.29/1.01  --qbf_elim_univ                         false
% 2.29/1.01  --qbf_dom_inst                          none
% 2.29/1.01  --qbf_dom_pre_inst                      false
% 2.29/1.01  --qbf_sk_in                             false
% 2.29/1.01  --qbf_pred_elim                         true
% 2.29/1.01  --qbf_split                             512
% 2.29/1.01  
% 2.29/1.01  ------ BMC1 Options
% 2.29/1.01  
% 2.29/1.01  --bmc1_incremental                      false
% 2.29/1.01  --bmc1_axioms                           reachable_all
% 2.29/1.01  --bmc1_min_bound                        0
% 2.29/1.01  --bmc1_max_bound                        -1
% 2.29/1.01  --bmc1_max_bound_default                -1
% 2.29/1.01  --bmc1_symbol_reachability              true
% 2.29/1.01  --bmc1_property_lemmas                  false
% 2.29/1.01  --bmc1_k_induction                      false
% 2.29/1.01  --bmc1_non_equiv_states                 false
% 2.29/1.01  --bmc1_deadlock                         false
% 2.29/1.01  --bmc1_ucm                              false
% 2.29/1.01  --bmc1_add_unsat_core                   none
% 2.29/1.01  --bmc1_unsat_core_children              false
% 2.29/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.01  --bmc1_out_stat                         full
% 2.29/1.01  --bmc1_ground_init                      false
% 2.29/1.01  --bmc1_pre_inst_next_state              false
% 2.29/1.01  --bmc1_pre_inst_state                   false
% 2.29/1.01  --bmc1_pre_inst_reach_state             false
% 2.29/1.01  --bmc1_out_unsat_core                   false
% 2.29/1.01  --bmc1_aig_witness_out                  false
% 2.29/1.01  --bmc1_verbose                          false
% 2.29/1.01  --bmc1_dump_clauses_tptp                false
% 2.29/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.01  --bmc1_dump_file                        -
% 2.29/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.01  --bmc1_ucm_extend_mode                  1
% 2.29/1.01  --bmc1_ucm_init_mode                    2
% 2.29/1.01  --bmc1_ucm_cone_mode                    none
% 2.29/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.01  --bmc1_ucm_relax_model                  4
% 2.29/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.01  --bmc1_ucm_layered_model                none
% 2.29/1.01  --bmc1_ucm_max_lemma_size               10
% 2.29/1.01  
% 2.29/1.01  ------ AIG Options
% 2.29/1.01  
% 2.29/1.01  --aig_mode                              false
% 2.29/1.01  
% 2.29/1.01  ------ Instantiation Options
% 2.29/1.01  
% 2.29/1.01  --instantiation_flag                    true
% 2.29/1.01  --inst_sos_flag                         false
% 2.29/1.01  --inst_sos_phase                        true
% 2.29/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.01  --inst_lit_sel_side                     none
% 2.29/1.01  --inst_solver_per_active                1400
% 2.29/1.01  --inst_solver_calls_frac                1.
% 2.29/1.01  --inst_passive_queue_type               priority_queues
% 2.29/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.01  --inst_passive_queues_freq              [25;2]
% 2.29/1.01  --inst_dismatching                      true
% 2.29/1.01  --inst_eager_unprocessed_to_passive     true
% 2.29/1.01  --inst_prop_sim_given                   true
% 2.29/1.01  --inst_prop_sim_new                     false
% 2.29/1.01  --inst_subs_new                         false
% 2.29/1.01  --inst_eq_res_simp                      false
% 2.29/1.01  --inst_subs_given                       false
% 2.29/1.01  --inst_orphan_elimination               true
% 2.29/1.01  --inst_learning_loop_flag               true
% 2.29/1.01  --inst_learning_start                   3000
% 2.29/1.01  --inst_learning_factor                  2
% 2.29/1.01  --inst_start_prop_sim_after_learn       3
% 2.29/1.01  --inst_sel_renew                        solver
% 2.29/1.01  --inst_lit_activity_flag                true
% 2.29/1.01  --inst_restr_to_given                   false
% 2.29/1.01  --inst_activity_threshold               500
% 2.29/1.01  --inst_out_proof                        true
% 2.29/1.01  
% 2.29/1.01  ------ Resolution Options
% 2.29/1.01  
% 2.29/1.01  --resolution_flag                       false
% 2.29/1.01  --res_lit_sel                           adaptive
% 2.29/1.01  --res_lit_sel_side                      none
% 2.29/1.01  --res_ordering                          kbo
% 2.29/1.01  --res_to_prop_solver                    active
% 2.29/1.01  --res_prop_simpl_new                    false
% 2.29/1.01  --res_prop_simpl_given                  true
% 2.29/1.01  --res_passive_queue_type                priority_queues
% 2.29/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.01  --res_passive_queues_freq               [15;5]
% 2.29/1.01  --res_forward_subs                      full
% 2.29/1.01  --res_backward_subs                     full
% 2.29/1.01  --res_forward_subs_resolution           true
% 2.29/1.01  --res_backward_subs_resolution          true
% 2.29/1.01  --res_orphan_elimination                true
% 2.29/1.01  --res_time_limit                        2.
% 2.29/1.01  --res_out_proof                         true
% 2.29/1.01  
% 2.29/1.01  ------ Superposition Options
% 2.29/1.01  
% 2.29/1.01  --superposition_flag                    true
% 2.29/1.01  --sup_passive_queue_type                priority_queues
% 2.29/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.01  --demod_completeness_check              fast
% 2.29/1.01  --demod_use_ground                      true
% 2.29/1.01  --sup_to_prop_solver                    passive
% 2.29/1.01  --sup_prop_simpl_new                    true
% 2.29/1.01  --sup_prop_simpl_given                  true
% 2.29/1.01  --sup_fun_splitting                     false
% 2.29/1.01  --sup_smt_interval                      50000
% 2.29/1.01  
% 2.29/1.01  ------ Superposition Simplification Setup
% 2.29/1.01  
% 2.29/1.01  --sup_indices_passive                   []
% 2.29/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_full_bw                           [BwDemod]
% 2.29/1.01  --sup_immed_triv                        [TrivRules]
% 2.29/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_immed_bw_main                     []
% 2.29/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.01  
% 2.29/1.01  ------ Combination Options
% 2.29/1.01  
% 2.29/1.01  --comb_res_mult                         3
% 2.29/1.01  --comb_sup_mult                         2
% 2.29/1.01  --comb_inst_mult                        10
% 2.29/1.01  
% 2.29/1.01  ------ Debug Options
% 2.29/1.01  
% 2.29/1.01  --dbg_backtrace                         false
% 2.29/1.01  --dbg_dump_prop_clauses                 false
% 2.29/1.01  --dbg_dump_prop_clauses_file            -
% 2.29/1.01  --dbg_out_stat                          false
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  ------ Proving...
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  % SZS status Theorem for theBenchmark.p
% 2.29/1.01  
% 2.29/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.29/1.01  
% 2.29/1.01  fof(f2,axiom,(
% 2.29/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f22,plain,(
% 2.29/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.29/1.01    inference(nnf_transformation,[],[f2])).
% 2.29/1.01  
% 2.29/1.01  fof(f35,plain,(
% 2.29/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.29/1.01    inference(cnf_transformation,[],[f22])).
% 2.29/1.01  
% 2.29/1.01  fof(f12,conjecture,(
% 2.29/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f13,negated_conjecture,(
% 2.29/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 2.29/1.01    inference(negated_conjecture,[],[f12])).
% 2.29/1.01  
% 2.29/1.01  fof(f19,plain,(
% 2.29/1.01    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f13])).
% 2.29/1.01  
% 2.29/1.01  fof(f28,plain,(
% 2.29/1.01    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(nnf_transformation,[],[f19])).
% 2.29/1.01  
% 2.29/1.01  fof(f29,plain,(
% 2.29/1.01    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(flattening,[],[f28])).
% 2.29/1.01  
% 2.29/1.01  fof(f30,plain,(
% 2.29/1.01    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.29/1.01    introduced(choice_axiom,[])).
% 2.29/1.01  
% 2.29/1.01  fof(f31,plain,(
% 2.29/1.01    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.29/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).
% 2.29/1.01  
% 2.29/1.01  fof(f52,plain,(
% 2.29/1.01    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.29/1.01    inference(cnf_transformation,[],[f31])).
% 2.29/1.01  
% 2.29/1.01  fof(f8,axiom,(
% 2.29/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f16,plain,(
% 2.29/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f8])).
% 2.29/1.01  
% 2.29/1.01  fof(f48,plain,(
% 2.29/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/1.01    inference(cnf_transformation,[],[f16])).
% 2.29/1.01  
% 2.29/1.01  fof(f53,plain,(
% 2.29/1.01    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 2.29/1.01    inference(cnf_transformation,[],[f31])).
% 2.29/1.01  
% 2.29/1.01  fof(f7,axiom,(
% 2.29/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f47,plain,(
% 2.29/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.29/1.01    inference(cnf_transformation,[],[f7])).
% 2.29/1.01  
% 2.29/1.01  fof(f9,axiom,(
% 2.29/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f17,plain,(
% 2.29/1.01    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f9])).
% 2.29/1.01  
% 2.29/1.01  fof(f49,plain,(
% 2.29/1.01    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/1.01    inference(cnf_transformation,[],[f17])).
% 2.29/1.01  
% 2.29/1.01  fof(f11,axiom,(
% 2.29/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f18,plain,(
% 2.29/1.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f11])).
% 2.29/1.01  
% 2.29/1.01  fof(f51,plain,(
% 2.29/1.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.29/1.01    inference(cnf_transformation,[],[f18])).
% 2.29/1.01  
% 2.29/1.01  fof(f4,axiom,(
% 2.29/1.01    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f14,plain,(
% 2.29/1.01    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f4])).
% 2.29/1.01  
% 2.29/1.01  fof(f38,plain,(
% 2.29/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.29/1.01    inference(cnf_transformation,[],[f14])).
% 2.29/1.01  
% 2.29/1.01  fof(f6,axiom,(
% 2.29/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f15,plain,(
% 2.29/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.29/1.01    inference(ennf_transformation,[],[f6])).
% 2.29/1.01  
% 2.29/1.01  fof(f27,plain,(
% 2.29/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.29/1.01    inference(nnf_transformation,[],[f15])).
% 2.29/1.01  
% 2.29/1.01  fof(f43,plain,(
% 2.29/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.29/1.01    inference(cnf_transformation,[],[f27])).
% 2.29/1.01  
% 2.29/1.01  fof(f10,axiom,(
% 2.29/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f50,plain,(
% 2.29/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.29/1.01    inference(cnf_transformation,[],[f10])).
% 2.29/1.01  
% 2.29/1.01  fof(f5,axiom,(
% 2.29/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f23,plain,(
% 2.29/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.29/1.01    inference(nnf_transformation,[],[f5])).
% 2.29/1.01  
% 2.29/1.01  fof(f24,plain,(
% 2.29/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.29/1.01    inference(rectify,[],[f23])).
% 2.29/1.01  
% 2.29/1.01  fof(f25,plain,(
% 2.29/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.29/1.01    introduced(choice_axiom,[])).
% 2.29/1.01  
% 2.29/1.01  fof(f26,plain,(
% 2.29/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.29/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.29/1.01  
% 2.29/1.01  fof(f39,plain,(
% 2.29/1.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.29/1.01    inference(cnf_transformation,[],[f26])).
% 2.29/1.01  
% 2.29/1.01  fof(f58,plain,(
% 2.29/1.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.29/1.01    inference(equality_resolution,[],[f39])).
% 2.29/1.01  
% 2.29/1.01  fof(f1,axiom,(
% 2.29/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.01  
% 2.29/1.01  fof(f20,plain,(
% 2.29/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/1.01    inference(nnf_transformation,[],[f1])).
% 2.29/1.01  
% 2.29/1.01  fof(f21,plain,(
% 2.29/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/1.01    inference(flattening,[],[f20])).
% 2.29/1.01  
% 2.29/1.01  fof(f34,plain,(
% 2.29/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.29/1.01    inference(cnf_transformation,[],[f21])).
% 2.29/1.01  
% 2.29/1.01  fof(f36,plain,(
% 2.29/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.29/1.01    inference(cnf_transformation,[],[f22])).
% 2.29/1.01  
% 2.29/1.01  fof(f32,plain,(
% 2.29/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.29/1.01    inference(cnf_transformation,[],[f21])).
% 2.29/1.01  
% 2.29/1.01  fof(f56,plain,(
% 2.29/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.29/1.01    inference(equality_resolution,[],[f32])).
% 2.29/1.01  
% 2.29/1.01  fof(f40,plain,(
% 2.29/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.29/1.01    inference(cnf_transformation,[],[f26])).
% 2.29/1.01  
% 2.29/1.01  fof(f57,plain,(
% 2.29/1.01    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.29/1.01    inference(equality_resolution,[],[f40])).
% 2.29/1.01  
% 2.29/1.01  fof(f44,plain,(
% 2.29/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.29/1.01    inference(cnf_transformation,[],[f27])).
% 2.29/1.01  
% 2.29/1.01  fof(f54,plain,(
% 2.29/1.01    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 2.29/1.01    inference(cnf_transformation,[],[f31])).
% 2.29/1.01  
% 2.29/1.01  cnf(c_4,plain,
% 2.29/1.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.29/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_4004,plain,
% 2.29/1.01      ( r1_tarski(sK1,X0) | k4_xboole_0(sK1,X0) != k1_xboole_0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_4006,plain,
% 2.29/1.01      ( r1_tarski(sK1,sK2) | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_4004]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_730,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1622,plain,
% 2.29/1.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_730]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3944,plain,
% 2.29/1.01      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3945,plain,
% 2.29/1.01      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_3944]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_22,negated_conjecture,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 2.29/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1250,plain,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_16,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.29/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1256,plain,
% 2.29/1.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.29/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2117,plain,
% 2.29/1.01      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_1250,c_1256]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_21,negated_conjecture,
% 2.29/1.01      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 2.29/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1251,plain,
% 2.29/1.01      ( k2_subset_1(sK1) = sK2
% 2.29/1.01      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_15,plain,
% 2.29/1.01      ( k2_subset_1(X0) = X0 ),
% 2.29/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1281,plain,
% 2.29/1.01      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 2.29/1.01      inference(demodulation,[status(thm)],[c_1251,c_15]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2282,plain,
% 2.29/1.01      ( sK2 = sK1 | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 2.29/1.01      inference(demodulation,[status(thm)],[c_2117,c_1281]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_17,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.29/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1255,plain,
% 2.29/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.29/1.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2300,plain,
% 2.29/1.01      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.29/1.01      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2117,c_1255]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_23,plain,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2687,plain,
% 2.29/1.01      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(global_propositional_subsumption,
% 2.29/1.01                [status(thm)],
% 2.29/1.01                [c_2300,c_23]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2694,plain,
% 2.29/1.01      ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2687,c_1256]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_19,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.29/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1253,plain,
% 2.29/1.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.29/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2046,plain,
% 2.29/1.01      ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_1250,c_1253]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2280,plain,
% 2.29/1.01      ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 2.29/1.01      inference(demodulation,[status(thm)],[c_2117,c_2046]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2699,plain,
% 2.29/1.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 2.29/1.01      inference(light_normalisation,[status(thm)],[c_2694,c_2280]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_6,plain,
% 2.29/1.01      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 2.29/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1265,plain,
% 2.29/1.01      ( k1_xboole_0 = X0
% 2.29/1.01      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3288,plain,
% 2.29/1.01      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 2.29/1.01      | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2699,c_1265]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3691,plain,
% 2.29/1.01      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 | sK2 = sK1 ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2282,c_3288]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_14,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.29/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1257,plain,
% 2.29/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.29/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.29/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2061,plain,
% 2.29/1.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_1250,c_1257]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1441,plain,
% 2.29/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 2.29/1.01      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1442,plain,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 2.29/1.01      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_18,plain,
% 2.29/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.29/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1496,plain,
% 2.29/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1497,plain,
% 2.29/1.01      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2434,plain,
% 2.29/1.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.29/1.01      inference(global_propositional_subsumption,
% 2.29/1.01                [status(thm)],
% 2.29/1.01                [c_2061,c_23,c_1442,c_1497]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_10,plain,
% 2.29/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.29/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1261,plain,
% 2.29/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.29/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2439,plain,
% 2.29/1.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2434,c_1261]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_0,plain,
% 2.29/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.29/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1270,plain,
% 2.29/1.01      ( X0 = X1
% 2.29/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.29/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2829,plain,
% 2.29/1.01      ( sK2 = sK1 | r1_tarski(sK1,sK2) != iProver_top ),
% 2.29/1.01      inference(superposition,[status(thm)],[c_2439,c_1270]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_29,plain,
% 2.29/1.01      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_31,plain,
% 2.29/1.01      ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_32,plain,
% 2.29/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.29/1.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_34,plain,
% 2.29/1.01      ( m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2)) = iProver_top
% 2.29/1.01      | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_67,plain,
% 2.29/1.01      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.29/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_69,plain,
% 2.29/1.01      ( k4_xboole_0(sK2,sK2) != k1_xboole_0
% 2.29/1.01      | r1_tarski(sK2,sK2) = iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_67]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3,plain,
% 2.29/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.29/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_71,plain,
% 2.29/1.01      ( ~ r1_tarski(sK2,sK2) | k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2,plain,
% 2.29/1.01      ( r1_tarski(X0,X0) ),
% 2.29/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_74,plain,
% 2.29/1.01      ( r1_tarski(sK2,sK2) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_78,plain,
% 2.29/1.01      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_9,plain,
% 2.29/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.29/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_183,plain,
% 2.29/1.01      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.29/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_184,plain,
% 2.29/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.29/1.01      inference(renaming,[status(thm)],[c_183]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_13,plain,
% 2.29/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.29/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_373,plain,
% 2.29/1.01      ( m1_subset_1(X0,X1)
% 2.29/1.01      | ~ r1_tarski(X2,X3)
% 2.29/1.01      | v1_xboole_0(X1)
% 2.29/1.01      | X0 != X2
% 2.29/1.01      | k1_zfmisc_1(X3) != X1 ),
% 2.29/1.01      inference(resolution_lifted,[status(thm)],[c_184,c_13]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_374,plain,
% 2.29/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | ~ r1_tarski(X0,X1)
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 2.29/1.01      inference(unflattening,[status(thm)],[c_373]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_375,plain,
% 2.29/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.29/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_377,plain,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top
% 2.29/1.01      | r1_tarski(sK2,sK2) != iProver_top
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_375]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_732,plain,
% 2.29/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.29/1.01      theory(equality) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_739,plain,
% 2.29/1.01      ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK2) | sK2 != sK2 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_732]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_20,negated_conjecture,
% 2.29/1.01      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 2.29/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1252,plain,
% 2.29/1.01      ( k2_subset_1(sK1) != sK2
% 2.29/1.01      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1306,plain,
% 2.29/1.01      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 2.29/1.01      inference(demodulation,[status(thm)],[c_1252,c_15]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1616,plain,
% 2.29/1.01      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1617,plain,
% 2.29/1.01      ( sK1 = X0
% 2.29/1.01      | r1_tarski(X0,sK1) != iProver_top
% 2.29/1.01      | r1_tarski(sK1,X0) != iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1619,plain,
% 2.29/1.01      ( sK1 = sK2
% 2.29/1.01      | r1_tarski(sK2,sK1) != iProver_top
% 2.29/1.01      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1617]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1900,plain,
% 2.29/1.01      ( ~ r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1904,plain,
% 2.29/1.01      ( r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) != iProver_top
% 2.29/1.01      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_737,plain,
% 2.29/1.01      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 2.29/1.01      theory(equality) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1993,plain,
% 2.29/1.01      ( k3_subset_1(sK1,sK2) = k3_subset_1(X0,X1)
% 2.29/1.01      | sK2 != X1
% 2.29/1.01      | sK1 != X0 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_737]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1998,plain,
% 2.29/1.01      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK2,sK2)
% 2.29/1.01      | sK2 != sK2
% 2.29/1.01      | sK1 != sK2 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1993]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2220,plain,
% 2.29/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(sK1)) | r1_tarski(X0,sK1) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2226,plain,
% 2.29/1.01      ( r2_hidden(X0,k1_zfmisc_1(sK1)) != iProver_top
% 2.29/1.01      | r1_tarski(X0,sK1) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2228,plain,
% 2.29/1.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 2.29/1.01      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_2226]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1716,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | r2_hidden(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2343,plain,
% 2.29/1.01      ( ~ m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1716]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2344,plain,
% 2.29/1.01      ( m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) != iProver_top
% 2.29/1.01      | r2_hidden(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_2343]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_734,plain,
% 2.29/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.29/1.01      theory(equality) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1467,plain,
% 2.29/1.01      ( m1_subset_1(X0,X1)
% 2.29/1.01      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))
% 2.29/1.01      | X0 != k3_subset_1(X2,X3)
% 2.29/1.01      | X1 != k1_zfmisc_1(X2) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_734]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1863,plain,
% 2.29/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.29/1.01      | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
% 2.29/1.01      | X0 != k3_subset_1(X1,X2)
% 2.29/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1467]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2862,plain,
% 2.29/1.01      ( ~ m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2))
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,X0)
% 2.29/1.01      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_1863]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2869,plain,
% 2.29/1.01      ( k3_subset_1(sK1,sK2) != k3_subset_1(sK2,X0)
% 2.29/1.01      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) != iProver_top
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.29/1.01      inference(predicate_to_equality,[status(thm)],[c_2862]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2871,plain,
% 2.29/1.01      ( k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
% 2.29/1.01      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2)) != iProver_top
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_2869]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3163,plain,
% 2.29/1.01      ( r1_tarski(sK1,sK2) != iProver_top ),
% 2.29/1.01      inference(global_propositional_subsumption,
% 2.29/1.01                [status(thm)],
% 2.29/1.01                [c_2829,c_23,c_31,c_34,c_69,c_71,c_74,c_78,c_377,c_739,
% 2.29/1.01                 c_1306,c_1442,c_1497,c_1619,c_1904,c_1998,c_2228,c_2344,
% 2.29/1.01                 c_2871]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_3165,plain,
% 2.29/1.01      ( ~ r1_tarski(sK1,sK2) ),
% 2.29/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3163]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2870,plain,
% 2.29/1.01      ( ~ m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | m1_subset_1(k3_subset_1(sK1,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
% 2.29/1.01      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_2862]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_729,plain,( X0 = X0 ),theory(equality) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_2213,plain,
% 2.29/1.01      ( sK1 = sK1 ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_729]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_1375,plain,
% 2.29/1.01      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK2 != sK1 ),
% 2.29/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1306]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_376,plain,
% 2.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
% 2.29/1.01      | ~ r1_tarski(sK2,sK2)
% 2.29/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_374]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_33,plain,
% 2.29/1.01      ( m1_subset_1(k3_subset_1(sK2,sK2),k1_zfmisc_1(sK2))
% 2.29/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(c_30,plain,
% 2.29/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
% 2.29/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 2.29/1.01  
% 2.29/1.01  cnf(contradiction,plain,
% 2.29/1.01      ( $false ),
% 2.29/1.01      inference(minisat,
% 2.29/1.01                [status(thm)],
% 2.29/1.01                [c_4006,c_3945,c_3691,c_3165,c_2870,c_2343,c_2213,c_1998,
% 2.29/1.01                 c_1900,c_1375,c_739,c_376,c_78,c_74,c_33,c_30]) ).
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.29/1.01  
% 2.29/1.01  ------                               Statistics
% 2.29/1.01  
% 2.29/1.01  ------ General
% 2.29/1.01  
% 2.29/1.01  abstr_ref_over_cycles:                  0
% 2.29/1.01  abstr_ref_under_cycles:                 0
% 2.29/1.01  gc_basic_clause_elim:                   0
% 2.29/1.01  forced_gc_time:                         0
% 2.29/1.01  parsing_time:                           0.006
% 2.29/1.01  unif_index_cands_time:                  0.
% 2.29/1.01  unif_index_add_time:                    0.
% 2.29/1.01  orderings_time:                         0.
% 2.29/1.01  out_proof_time:                         0.011
% 2.29/1.01  total_time:                             0.106
% 2.29/1.01  num_of_symbols:                         43
% 2.29/1.01  num_of_terms:                           2748
% 2.29/1.01  
% 2.29/1.01  ------ Preprocessing
% 2.29/1.01  
% 2.29/1.01  num_of_splits:                          0
% 2.29/1.01  num_of_split_atoms:                     0
% 2.29/1.01  num_of_reused_defs:                     0
% 2.29/1.01  num_eq_ax_congr_red:                    12
% 2.29/1.01  num_of_sem_filtered_clauses:            1
% 2.29/1.01  num_of_subtypes:                        0
% 2.29/1.01  monotx_restored_types:                  0
% 2.29/1.01  sat_num_of_epr_types:                   0
% 2.29/1.01  sat_num_of_non_cyclic_types:            0
% 2.29/1.01  sat_guarded_non_collapsed_types:        0
% 2.29/1.01  num_pure_diseq_elim:                    0
% 2.29/1.01  simp_replaced_by:                       0
% 2.29/1.01  res_preprocessed:                       107
% 2.29/1.01  prep_upred:                             0
% 2.29/1.01  prep_unflattend:                        24
% 2.29/1.01  smt_new_axioms:                         0
% 2.29/1.01  pred_elim_cands:                        4
% 2.29/1.01  pred_elim:                              0
% 2.29/1.01  pred_elim_cl:                           0
% 2.29/1.01  pred_elim_cycles:                       2
% 2.29/1.01  merged_defs:                            24
% 2.29/1.01  merged_defs_ncl:                        0
% 2.29/1.01  bin_hyper_res:                          24
% 2.29/1.01  prep_cycles:                            4
% 2.29/1.01  pred_elim_time:                         0.002
% 2.29/1.01  splitting_time:                         0.
% 2.29/1.01  sem_filter_time:                        0.
% 2.29/1.01  monotx_time:                            0.
% 2.29/1.01  subtype_inf_time:                       0.
% 2.29/1.01  
% 2.29/1.01  ------ Problem properties
% 2.29/1.01  
% 2.29/1.01  clauses:                                22
% 2.29/1.01  conjectures:                            3
% 2.29/1.01  epr:                                    7
% 2.29/1.01  horn:                                   18
% 2.29/1.01  ground:                                 3
% 2.29/1.01  unary:                                  5
% 2.29/1.01  binary:                                 10
% 2.29/1.01  lits:                                   46
% 2.29/1.01  lits_eq:                                11
% 2.29/1.01  fd_pure:                                0
% 2.29/1.01  fd_pseudo:                              0
% 2.29/1.01  fd_cond:                                1
% 2.29/1.01  fd_pseudo_cond:                         3
% 2.29/1.01  ac_symbols:                             0
% 2.29/1.01  
% 2.29/1.01  ------ Propositional Solver
% 2.29/1.01  
% 2.29/1.01  prop_solver_calls:                      28
% 2.29/1.01  prop_fast_solver_calls:                 618
% 2.29/1.01  smt_solver_calls:                       0
% 2.29/1.01  smt_fast_solver_calls:                  0
% 2.29/1.01  prop_num_of_clauses:                    1387
% 2.29/1.01  prop_preprocess_simplified:             4541
% 2.29/1.01  prop_fo_subsumed:                       6
% 2.29/1.01  prop_solver_time:                       0.
% 2.29/1.01  smt_solver_time:                        0.
% 2.29/1.01  smt_fast_solver_time:                   0.
% 2.29/1.01  prop_fast_solver_time:                  0.
% 2.29/1.01  prop_unsat_core_time:                   0.
% 2.29/1.01  
% 2.29/1.01  ------ QBF
% 2.29/1.01  
% 2.29/1.01  qbf_q_res:                              0
% 2.29/1.01  qbf_num_tautologies:                    0
% 2.29/1.01  qbf_prep_cycles:                        0
% 2.29/1.01  
% 2.29/1.01  ------ BMC1
% 2.29/1.01  
% 2.29/1.01  bmc1_current_bound:                     -1
% 2.29/1.01  bmc1_last_solved_bound:                 -1
% 2.29/1.01  bmc1_unsat_core_size:                   -1
% 2.29/1.01  bmc1_unsat_core_parents_size:           -1
% 2.29/1.01  bmc1_merge_next_fun:                    0
% 2.29/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.29/1.01  
% 2.29/1.01  ------ Instantiation
% 2.29/1.01  
% 2.29/1.01  inst_num_of_clauses:                    421
% 2.29/1.01  inst_num_in_passive:                    70
% 2.29/1.01  inst_num_in_active:                     215
% 2.29/1.01  inst_num_in_unprocessed:                135
% 2.29/1.01  inst_num_of_loops:                      253
% 2.29/1.01  inst_num_of_learning_restarts:          0
% 2.29/1.01  inst_num_moves_active_passive:          34
% 2.29/1.01  inst_lit_activity:                      0
% 2.29/1.01  inst_lit_activity_moves:                0
% 2.29/1.01  inst_num_tautologies:                   0
% 2.29/1.01  inst_num_prop_implied:                  0
% 2.29/1.01  inst_num_existing_simplified:           0
% 2.29/1.01  inst_num_eq_res_simplified:             0
% 2.29/1.01  inst_num_child_elim:                    0
% 2.29/1.01  inst_num_of_dismatching_blockings:      166
% 2.29/1.01  inst_num_of_non_proper_insts:           439
% 2.29/1.01  inst_num_of_duplicates:                 0
% 2.29/1.01  inst_inst_num_from_inst_to_res:         0
% 2.29/1.01  inst_dismatching_checking_time:         0.
% 2.29/1.01  
% 2.29/1.01  ------ Resolution
% 2.29/1.01  
% 2.29/1.01  res_num_of_clauses:                     0
% 2.29/1.01  res_num_in_passive:                     0
% 2.29/1.01  res_num_in_active:                      0
% 2.29/1.01  res_num_of_loops:                       111
% 2.29/1.01  res_forward_subset_subsumed:            21
% 2.29/1.01  res_backward_subset_subsumed:           0
% 2.29/1.01  res_forward_subsumed:                   0
% 2.29/1.01  res_backward_subsumed:                  0
% 2.29/1.01  res_forward_subsumption_resolution:     2
% 2.29/1.01  res_backward_subsumption_resolution:    0
% 2.29/1.01  res_clause_to_clause_subsumption:       217
% 2.29/1.01  res_orphan_elimination:                 0
% 2.29/1.01  res_tautology_del:                      92
% 2.29/1.01  res_num_eq_res_simplified:              0
% 2.29/1.01  res_num_sel_changes:                    0
% 2.29/1.01  res_moves_from_active_to_pass:          0
% 2.29/1.01  
% 2.29/1.01  ------ Superposition
% 2.29/1.01  
% 2.29/1.01  sup_time_total:                         0.
% 2.29/1.01  sup_time_generating:                    0.
% 2.29/1.01  sup_time_sim_full:                      0.
% 2.29/1.01  sup_time_sim_immed:                     0.
% 2.29/1.01  
% 2.29/1.01  sup_num_of_clauses:                     61
% 2.29/1.01  sup_num_in_active:                      46
% 2.29/1.01  sup_num_in_passive:                     15
% 2.29/1.01  sup_num_of_loops:                       50
% 2.29/1.01  sup_fw_superposition:                   30
% 2.29/1.01  sup_bw_superposition:                   42
% 2.29/1.01  sup_immediate_simplified:               17
% 2.29/1.01  sup_given_eliminated:                   0
% 2.29/1.01  comparisons_done:                       0
% 2.29/1.01  comparisons_avoided:                    7
% 2.29/1.01  
% 2.29/1.01  ------ Simplifications
% 2.29/1.01  
% 2.29/1.01  
% 2.29/1.01  sim_fw_subset_subsumed:                 8
% 2.29/1.01  sim_bw_subset_subsumed:                 0
% 2.29/1.01  sim_fw_subsumed:                        3
% 2.29/1.01  sim_bw_subsumed:                        0
% 2.29/1.01  sim_fw_subsumption_res:                 0
% 2.29/1.01  sim_bw_subsumption_res:                 0
% 2.29/1.01  sim_tautology_del:                      4
% 2.29/1.01  sim_eq_tautology_del:                   7
% 2.29/1.01  sim_eq_res_simp:                        0
% 2.29/1.01  sim_fw_demodulated:                     2
% 2.29/1.01  sim_bw_demodulated:                     4
% 2.29/1.01  sim_light_normalised:                   6
% 2.29/1.01  sim_joinable_taut:                      0
% 2.29/1.01  sim_joinable_simp:                      0
% 2.29/1.01  sim_ac_normalised:                      0
% 2.29/1.01  sim_smt_subsumption:                    0
% 2.29/1.01  
%------------------------------------------------------------------------------
