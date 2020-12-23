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
% DateTime   : Thu Dec  3 11:40:58 EST 2020

% Result     : Theorem 11.79s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 253 expanded)
%              Number of clauses        :   59 (  86 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  280 ( 703 expanded)
%              Number of equality atoms :  108 ( 219 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK3,k3_subset_1(X0,X1))
        & ~ r2_hidden(sK3,X1)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(X0,sK2))
            & ~ r2_hidden(X2,sK2)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK1,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(sK1)) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK3,k3_subset_1(sK1,sK2))
    & ~ r2_hidden(sK3,sK2)
    & m1_subset_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(sK1))
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f67,plain,(
    ~ r2_hidden(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_695,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_701,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4389,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_701])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_900,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_901,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_963,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_964,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_5750,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4389,c_28,c_901,c_964])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_705,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14817,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5750,c_705])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_709,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14981,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_14817,c_709])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_240,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_11,c_0])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1161,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_244,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_11,c_0])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_739,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_244,c_1,c_12])).

cnf(c_1174,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_739,c_0])).

cnf(c_1443,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1161,c_1174])).

cnf(c_28310,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_240,c_1443])).

cnf(c_28318,plain,
    ( k2_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_14981,c_28310])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28324,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_28318,c_9,c_12])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0)))) = k3_subset_1(X1,X0) ),
    inference(theory_normalisation,[status(thm)],[c_21,c_11,c_0])).

cnf(c_700,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0)))) = k3_subset_1(X1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_2168,plain,
    ( k5_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_subset_1(X1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_700,c_1443])).

cnf(c_2174,plain,
    ( k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_695,c_2168])).

cnf(c_28777,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_28324,c_2174])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_698,plain,
    ( r2_hidden(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29362,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28777,c_698])).

cnf(c_29366,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_29362])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1102,plain,
    ( r2_hidden(sK3,X0)
    | r2_hidden(sK3,k5_xboole_0(sK1,X0))
    | ~ r2_hidden(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3070,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_3071,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK1,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3070])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_931,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_932,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_897,plain,
    ( ~ m1_subset_1(sK3,sK1)
    | r2_hidden(sK3,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_898,plain,
    ( m1_subset_1(sK3,sK1) != iProver_top
    | r2_hidden(sK3,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29366,c_3071,c_932,c_898,c_30,c_29,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.79/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.79/1.99  
% 11.79/1.99  ------  iProver source info
% 11.79/1.99  
% 11.79/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.79/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.79/1.99  git: non_committed_changes: false
% 11.79/1.99  git: last_make_outside_of_git: false
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  ------ Parsing...
% 11.79/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.79/1.99  ------ Proving...
% 11.79/1.99  ------ Problem Properties 
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  clauses                                 28
% 11.79/1.99  conjectures                             5
% 11.79/1.99  EPR                                     8
% 11.79/1.99  Horn                                    22
% 11.79/1.99  unary                                   13
% 11.79/1.99  binary                                  5
% 11.79/1.99  lits                                    53
% 11.79/1.99  lits eq                                 13
% 11.79/1.99  fd_pure                                 0
% 11.79/1.99  fd_pseudo                               0
% 11.79/1.99  fd_cond                                 1
% 11.79/1.99  fd_pseudo_cond                          2
% 11.79/1.99  AC symbols                              1
% 11.79/1.99  
% 11.79/1.99  ------ Input Options Time Limit: Unbounded
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  Current options:
% 11.79/1.99  ------ 
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  ------ Proving...
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  % SZS status Theorem for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  fof(f1,axiom,(
% 11.79/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f38,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f1])).
% 11.79/1.99  
% 11.79/1.99  fof(f17,conjecture,(
% 11.79/1.99    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f18,negated_conjecture,(
% 11.79/1.99    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 11.79/1.99    inference(negated_conjecture,[],[f17])).
% 11.79/1.99  
% 11.79/1.99  fof(f26,plain,(
% 11.79/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 11.79/1.99    inference(ennf_transformation,[],[f18])).
% 11.79/1.99  
% 11.79/1.99  fof(f27,plain,(
% 11.79/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 11.79/1.99    inference(flattening,[],[f26])).
% 11.79/1.99  
% 11.79/1.99  fof(f36,plain,(
% 11.79/1.99    ( ! [X0,X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK3,k3_subset_1(X0,X1)) & ~r2_hidden(sK3,X1) & m1_subset_1(sK3,X0))) )),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f35,plain,(
% 11.79/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,sK2)) & ~r2_hidden(X2,sK2) & m1_subset_1(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f34,plain,(
% 11.79/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK1,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(sK1))) & k1_xboole_0 != sK1)),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f37,plain,(
% 11.79/1.99    ((~r2_hidden(sK3,k3_subset_1(sK1,sK2)) & ~r2_hidden(sK3,sK2) & m1_subset_1(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))) & k1_xboole_0 != sK1),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).
% 11.79/1.99  
% 11.79/1.99  fof(f64,plain,(
% 11.79/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.79/1.99    inference(cnf_transformation,[],[f37])).
% 11.79/1.99  
% 11.79/1.99  fof(f14,axiom,(
% 11.79/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f24,plain,(
% 11.79/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.79/1.99    inference(ennf_transformation,[],[f14])).
% 11.79/1.99  
% 11.79/1.99  fof(f33,plain,(
% 11.79/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.79/1.99    inference(nnf_transformation,[],[f24])).
% 11.79/1.99  
% 11.79/1.99  fof(f57,plain,(
% 11.79/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f33])).
% 11.79/1.99  
% 11.79/1.99  fof(f16,axiom,(
% 11.79/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f62,plain,(
% 11.79/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f16])).
% 11.79/1.99  
% 11.79/1.99  fof(f13,axiom,(
% 11.79/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f29,plain,(
% 11.79/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.79/1.99    inference(nnf_transformation,[],[f13])).
% 11.79/1.99  
% 11.79/1.99  fof(f30,plain,(
% 11.79/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.79/1.99    inference(rectify,[],[f29])).
% 11.79/1.99  
% 11.79/1.99  fof(f31,plain,(
% 11.79/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f32,plain,(
% 11.79/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 11.79/1.99  
% 11.79/1.99  fof(f53,plain,(
% 11.79/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.79/1.99    inference(cnf_transformation,[],[f32])).
% 11.79/1.99  
% 11.79/1.99  fof(f73,plain,(
% 11.79/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.79/1.99    inference(equality_resolution,[],[f53])).
% 11.79/1.99  
% 11.79/1.99  fof(f7,axiom,(
% 11.79/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f23,plain,(
% 11.79/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.79/1.99    inference(ennf_transformation,[],[f7])).
% 11.79/1.99  
% 11.79/1.99  fof(f47,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f23])).
% 11.79/1.99  
% 11.79/1.99  fof(f9,axiom,(
% 11.79/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f49,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f9])).
% 11.79/1.99  
% 11.79/1.99  fof(f6,axiom,(
% 11.79/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f46,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f6])).
% 11.79/1.99  
% 11.79/1.99  fof(f12,axiom,(
% 11.79/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f52,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f12])).
% 11.79/1.99  
% 11.79/1.99  fof(f68,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 11.79/1.99    inference(definition_unfolding,[],[f46,f52])).
% 11.79/1.99  
% 11.79/1.99  fof(f70,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))))) )),
% 11.79/1.99    inference(definition_unfolding,[],[f49,f68])).
% 11.79/1.99  
% 11.79/1.99  fof(f10,axiom,(
% 11.79/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f50,plain,(
% 11.79/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f10])).
% 11.79/1.99  
% 11.79/1.99  fof(f11,axiom,(
% 11.79/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f51,plain,(
% 11.79/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f11])).
% 11.79/1.99  
% 11.79/1.99  fof(f3,axiom,(
% 11.79/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f20,plain,(
% 11.79/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.79/1.99    inference(rectify,[],[f3])).
% 11.79/1.99  
% 11.79/1.99  fof(f40,plain,(
% 11.79/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f20])).
% 11.79/1.99  
% 11.79/1.99  fof(f69,plain,(
% 11.79/1.99    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 11.79/1.99    inference(definition_unfolding,[],[f40,f52])).
% 11.79/1.99  
% 11.79/1.99  fof(f2,axiom,(
% 11.79/1.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f19,plain,(
% 11.79/1.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.79/1.99    inference(rectify,[],[f2])).
% 11.79/1.99  
% 11.79/1.99  fof(f39,plain,(
% 11.79/1.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f19])).
% 11.79/1.99  
% 11.79/1.99  fof(f8,axiom,(
% 11.79/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f48,plain,(
% 11.79/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f8])).
% 11.79/1.99  
% 11.79/1.99  fof(f15,axiom,(
% 11.79/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f25,plain,(
% 11.79/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.79/1.99    inference(ennf_transformation,[],[f15])).
% 11.79/1.99  
% 11.79/1.99  fof(f61,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f25])).
% 11.79/1.99  
% 11.79/1.99  fof(f71,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.79/1.99    inference(definition_unfolding,[],[f61,f68])).
% 11.79/1.99  
% 11.79/1.99  fof(f67,plain,(
% 11.79/1.99    ~r2_hidden(sK3,k3_subset_1(sK1,sK2))),
% 11.79/1.99    inference(cnf_transformation,[],[f37])).
% 11.79/1.99  
% 11.79/1.99  fof(f5,axiom,(
% 11.79/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f22,plain,(
% 11.79/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 11.79/1.99    inference(ennf_transformation,[],[f5])).
% 11.79/1.99  
% 11.79/1.99  fof(f28,plain,(
% 11.79/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 11.79/1.99    inference(nnf_transformation,[],[f22])).
% 11.79/1.99  
% 11.79/1.99  fof(f44,plain,(
% 11.79/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f28])).
% 11.79/1.99  
% 11.79/1.99  fof(f4,axiom,(
% 11.79/1.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.79/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f21,plain,(
% 11.79/1.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.79/1.99    inference(ennf_transformation,[],[f4])).
% 11.79/1.99  
% 11.79/1.99  fof(f41,plain,(
% 11.79/1.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f21])).
% 11.79/1.99  
% 11.79/1.99  fof(f66,plain,(
% 11.79/1.99    ~r2_hidden(sK3,sK2)),
% 11.79/1.99    inference(cnf_transformation,[],[f37])).
% 11.79/1.99  
% 11.79/1.99  fof(f65,plain,(
% 11.79/1.99    m1_subset_1(sK3,sK1)),
% 11.79/1.99    inference(cnf_transformation,[],[f37])).
% 11.79/1.99  
% 11.79/1.99  fof(f63,plain,(
% 11.79/1.99    k1_xboole_0 != sK1),
% 11.79/1.99    inference(cnf_transformation,[],[f37])).
% 11.79/1.99  
% 11.79/1.99  cnf(c_0,plain,
% 11.79/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.79/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_26,negated_conjecture,
% 11.79/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_695,plain,
% 11.79/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_20,plain,
% 11.79/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_701,plain,
% 11.79/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.79/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.79/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_4389,plain,
% 11.79/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 11.79/1.99      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_695,c_701]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28,plain,
% 11.79/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_900,plain,
% 11.79/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 11.79/1.99      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 11.79/1.99      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_901,plain,
% 11.79/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 11.79/1.99      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 11.79/1.99      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_22,plain,
% 11.79/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_963,plain,
% 11.79/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_964,plain,
% 11.79/1.99      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5750,plain,
% 11.79/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.79/1.99      inference(global_propositional_subsumption,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_4389,c_28,c_901,c_964]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_16,plain,
% 11.79/1.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_705,plain,
% 11.79/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.79/1.99      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_14817,plain,
% 11.79/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_5750,c_705]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_8,plain,
% 11.79/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.79/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_709,plain,
% 11.79/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_14981,plain,
% 11.79/1.99      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_14817,c_709]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_10,plain,
% 11.79/1.99      ( k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_11,plain,
% 11.79/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_240,plain,
% 11.79/1.99      ( k2_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
% 11.79/1.99      inference(theory_normalisation,[status(thm)],[c_10,c_11,c_0]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_12,plain,
% 11.79/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1161,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2,plain,
% 11.79/1.99      ( k5_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_244,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0))) = X0 ),
% 11.79/1.99      inference(theory_normalisation,[status(thm)],[c_2,c_11,c_0]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1,plain,
% 11.79/1.99      ( k2_xboole_0(X0,X0) = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_739,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.79/1.99      inference(light_normalisation,[status(thm)],[c_244,c_1,c_12]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1174,plain,
% 11.79/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_739,c_0]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1443,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_1161,c_1174]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28310,plain,
% 11.79/1.99      ( k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_240,c_1443]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28318,plain,
% 11.79/1.99      ( k2_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,sK2) ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_14981,c_28310]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_9,plain,
% 11.79/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28324,plain,
% 11.79/1.99      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_28318,c_9,c_12]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_21,plain,
% 11.79/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.79/1.99      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
% 11.79/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_239,plain,
% 11.79/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.79/1.99      | k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0)))) = k3_subset_1(X1,X0) ),
% 11.79/1.99      inference(theory_normalisation,[status(thm)],[c_21,c_11,c_0]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_700,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0)))) = k3_subset_1(X1,X0)
% 11.79/1.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2168,plain,
% 11.79/1.99      ( k5_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_subset_1(X1,X0)
% 11.79/1.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_700,c_1443]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2174,plain,
% 11.79/1.99      ( k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_695,c_2168]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28777,plain,
% 11.79/1.99      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_28324,c_2174]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_23,negated_conjecture,
% 11.79/1.99      ( ~ r2_hidden(sK3,k3_subset_1(sK1,sK2)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_698,plain,
% 11.79/1.99      ( r2_hidden(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_29362,plain,
% 11.79/1.99      ( r2_hidden(sK3,k5_xboole_0(sK2,sK1)) != iProver_top ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_28777,c_698]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_29366,plain,
% 11.79/1.99      ( r2_hidden(sK3,k5_xboole_0(sK1,sK2)) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_0,c_29362]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5,plain,
% 11.79/1.99      ( ~ r2_hidden(X0,X1)
% 11.79/1.99      | r2_hidden(X0,X2)
% 11.79/1.99      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1102,plain,
% 11.79/1.99      ( r2_hidden(sK3,X0)
% 11.79/1.99      | r2_hidden(sK3,k5_xboole_0(sK1,X0))
% 11.79/1.99      | ~ r2_hidden(sK3,sK1) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3070,plain,
% 11.79/1.99      ( r2_hidden(sK3,k5_xboole_0(sK1,sK2))
% 11.79/1.99      | r2_hidden(sK3,sK2)
% 11.79/1.99      | ~ r2_hidden(sK3,sK1) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_1102]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3071,plain,
% 11.79/1.99      ( r2_hidden(sK3,k5_xboole_0(sK1,sK2)) = iProver_top
% 11.79/1.99      | r2_hidden(sK3,sK2) = iProver_top
% 11.79/1.99      | r2_hidden(sK3,sK1) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_3070]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3,plain,
% 11.79/1.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_931,plain,
% 11.79/1.99      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_932,plain,
% 11.79/1.99      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_897,plain,
% 11.79/1.99      ( ~ m1_subset_1(sK3,sK1) | r2_hidden(sK3,sK1) | v1_xboole_0(sK1) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_898,plain,
% 11.79/1.99      ( m1_subset_1(sK3,sK1) != iProver_top
% 11.79/1.99      | r2_hidden(sK3,sK1) = iProver_top
% 11.79/1.99      | v1_xboole_0(sK1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_24,negated_conjecture,
% 11.79/1.99      ( ~ r2_hidden(sK3,sK2) ),
% 11.79/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_30,plain,
% 11.79/1.99      ( r2_hidden(sK3,sK2) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_25,negated_conjecture,
% 11.79/1.99      ( m1_subset_1(sK3,sK1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_29,plain,
% 11.79/1.99      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_27,negated_conjecture,
% 11.79/1.99      ( k1_xboole_0 != sK1 ),
% 11.79/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(contradiction,plain,
% 11.79/1.99      ( $false ),
% 11.79/1.99      inference(minisat,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_29366,c_3071,c_932,c_898,c_30,c_29,c_27]) ).
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  ------                               Statistics
% 11.79/1.99  
% 11.79/1.99  ------ Selected
% 11.79/1.99  
% 11.79/1.99  total_time:                             1.273
% 11.79/1.99  
%------------------------------------------------------------------------------
