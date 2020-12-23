%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:02 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 746 expanded)
%              Number of clauses        :   74 ( 269 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   23
%              Number of atoms          :  297 (2007 expanded)
%              Number of equality atoms :  136 ( 716 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
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
    inference(nnf_transformation,[],[f12])).

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
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f39])).

fof(f59,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f61,f61])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f44,f39,f39])).

fof(f60,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1057,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_473,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_298,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_299,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_305,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_299,c_21])).

cnf(c_605,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_305])).

cnf(c_606,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1049,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1242,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1049])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1058,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3261,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1242,c_1058])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7645,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3261,c_2])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_311,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_312,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_1116,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_312])).

cnf(c_7671,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7645,c_1116])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1054,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1062,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1054,c_19])).

cnf(c_3258,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_1062,c_1058])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1056,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2670,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1056])).

cnf(c_3538,plain,
    ( sK2 = sK1
    | r1_tarski(k5_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_2670])).

cnf(c_3772,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_3538,c_1058])).

cnf(c_7785,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_7671,c_3772])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1503,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_4189,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_1503])).

cnf(c_7643,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3261,c_4189])).

cnf(c_7646,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_7643,c_7645])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1061,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_10])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1059,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_279,c_21])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_475,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_476,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_514,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_289,c_476])).

cnf(c_1053,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_2544,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_1059,c_1053])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1433,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_2160,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1433,c_2])).

cnf(c_2558,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2160,c_0])).

cnf(c_2563,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2558,c_2160])).

cnf(c_2564,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2563,c_1061,c_2544])).

cnf(c_3255,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1059,c_1058])).

cnf(c_5222,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2544,c_2544,c_2564,c_3255])).

cnf(c_7647,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_7646,c_1061,c_5222])).

cnf(c_7816,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7785,c_7645,c_7647])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1055,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1063,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1055,c_19])).

cnf(c_7809,plain,
    ( sK2 != sK1
    | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7671,c_1063])).

cnf(c_7835,plain,
    ( sK1 != sK1
    | r1_tarski(k5_xboole_0(sK1,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7816,c_7809])).

cnf(c_7836,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7835])).

cnf(c_7837,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7836,c_5222])).

cnf(c_7954,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1057,c_7837])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.57/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.99  
% 3.57/0.99  ------  iProver source info
% 3.57/0.99  
% 3.57/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.99  git: non_committed_changes: false
% 3.57/0.99  git: last_make_outside_of_git: false
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    ""
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         true
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     num_symb
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       true
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     true
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_input_bw                          []
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  ------ Parsing...
% 3.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.99  ------ Proving...
% 3.57/0.99  ------ Problem Properties 
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  clauses                                 19
% 3.57/0.99  conjectures                             2
% 3.57/0.99  EPR                                     3
% 3.57/0.99  Horn                                    17
% 3.57/0.99  unary                                   9
% 3.57/0.99  binary                                  6
% 3.57/0.99  lits                                    33
% 3.57/0.99  lits eq                                 18
% 3.57/0.99  fd_pure                                 0
% 3.57/0.99  fd_pseudo                               0
% 3.57/0.99  fd_cond                                 0
% 3.57/0.99  fd_pseudo_cond                          1
% 3.57/0.99  AC symbols                              0
% 3.57/0.99  
% 3.57/0.99  ------ Schedule dynamic 5 is on 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  Current options:
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    ""
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         true
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     none
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       false
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     true
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_input_bw                          []
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ Proving...
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS status Theorem for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99   Resolution empty clause
% 3.57/0.99  
% 3.57/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  fof(f7,axiom,(
% 3.57/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f42,plain,(
% 3.57/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f7])).
% 3.57/0.99  
% 3.57/0.99  fof(f12,axiom,(
% 3.57/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f25,plain,(
% 3.57/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.99    inference(nnf_transformation,[],[f12])).
% 3.57/0.99  
% 3.57/0.99  fof(f26,plain,(
% 3.57/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.99    inference(rectify,[],[f25])).
% 3.57/0.99  
% 3.57/0.99  fof(f27,plain,(
% 3.57/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f28,plain,(
% 3.57/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.57/0.99  
% 3.57/0.99  fof(f47,plain,(
% 3.57/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.57/0.99    inference(cnf_transformation,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f71,plain,(
% 3.57/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.57/0.99    inference(equality_resolution,[],[f47])).
% 3.57/0.99  
% 3.57/0.99  fof(f13,axiom,(
% 3.57/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f20,plain,(
% 3.57/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f13])).
% 3.57/0.99  
% 3.57/0.99  fof(f29,plain,(
% 3.57/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.57/0.99    inference(nnf_transformation,[],[f20])).
% 3.57/0.99  
% 3.57/0.99  fof(f51,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f29])).
% 3.57/0.99  
% 3.57/0.99  fof(f17,conjecture,(
% 3.57/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f18,negated_conjecture,(
% 3.57/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.57/0.99    inference(negated_conjecture,[],[f17])).
% 3.57/0.99  
% 3.57/0.99  fof(f22,plain,(
% 3.57/0.99    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f18])).
% 3.57/0.99  
% 3.57/0.99  fof(f30,plain,(
% 3.57/0.99    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.99    inference(nnf_transformation,[],[f22])).
% 3.57/0.99  
% 3.57/0.99  fof(f31,plain,(
% 3.57/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.99    inference(flattening,[],[f30])).
% 3.57/0.99  
% 3.57/0.99  fof(f32,plain,(
% 3.57/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f33,plain,(
% 3.57/0.99    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).
% 3.57/0.99  
% 3.57/0.99  fof(f58,plain,(
% 3.57/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f16,axiom,(
% 3.57/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f57,plain,(
% 3.57/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f16])).
% 3.57/0.99  
% 3.57/0.99  fof(f6,axiom,(
% 3.57/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f19,plain,(
% 3.57/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.57/0.99    inference(ennf_transformation,[],[f6])).
% 3.57/0.99  
% 3.57/0.99  fof(f41,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f19])).
% 3.57/0.99  
% 3.57/0.99  fof(f2,axiom,(
% 3.57/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f35,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f2])).
% 3.57/0.99  
% 3.57/0.99  fof(f15,axiom,(
% 3.57/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f21,plain,(
% 3.57/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f15])).
% 3.57/0.99  
% 3.57/0.99  fof(f56,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f21])).
% 3.57/0.99  
% 3.57/0.99  fof(f4,axiom,(
% 3.57/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f39,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f4])).
% 3.57/0.99  
% 3.57/0.99  fof(f67,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f56,f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f59,plain,(
% 3.57/0.99    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f14,axiom,(
% 3.57/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f55,plain,(
% 3.57/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f14])).
% 3.57/0.99  
% 3.57/0.99  fof(f8,axiom,(
% 3.57/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f43,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f8])).
% 3.57/0.99  
% 3.57/0.99  fof(f65,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f43,f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f1,axiom,(
% 3.57/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f34,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f1])).
% 3.57/0.99  
% 3.57/0.99  fof(f11,axiom,(
% 3.57/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f46,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f11])).
% 3.57/0.99  
% 3.57/0.99  fof(f61,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f46,f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f63,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f34,f61,f61])).
% 3.57/0.99  
% 3.57/0.99  fof(f5,axiom,(
% 3.57/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f40,plain,(
% 3.57/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f5])).
% 3.57/0.99  
% 3.57/0.99  fof(f64,plain,(
% 3.57/0.99    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f40,f61])).
% 3.57/0.99  
% 3.57/0.99  fof(f10,axiom,(
% 3.57/0.99    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f45,plain,(
% 3.57/0.99    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f10])).
% 3.57/0.99  
% 3.57/0.99  fof(f66,plain,(
% 3.57/0.99    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f45,f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f3,axiom,(
% 3.57/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f23,plain,(
% 3.57/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.99    inference(nnf_transformation,[],[f3])).
% 3.57/0.99  
% 3.57/0.99  fof(f24,plain,(
% 3.57/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.99    inference(flattening,[],[f23])).
% 3.57/0.99  
% 3.57/0.99  fof(f36,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.57/0.99    inference(cnf_transformation,[],[f24])).
% 3.57/0.99  
% 3.57/0.99  fof(f69,plain,(
% 3.57/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.57/0.99    inference(equality_resolution,[],[f36])).
% 3.57/0.99  
% 3.57/0.99  fof(f52,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f29])).
% 3.57/0.99  
% 3.57/0.99  fof(f48,plain,(
% 3.57/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.57/0.99    inference(cnf_transformation,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f70,plain,(
% 3.57/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f9,axiom,(
% 3.57/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f44,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f9])).
% 3.57/0.99  
% 3.57/0.99  fof(f62,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.57/0.99    inference(definition_unfolding,[],[f44,f39,f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f60,plain,(
% 3.57/0.99    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1057,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_473,plain,
% 3.57/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.57/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_474,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_473]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_18,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_24,negated_conjecture,
% 3.57/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_298,plain,
% 3.57/0.99      ( r2_hidden(X0,X1)
% 3.57/0.99      | v1_xboole_0(X1)
% 3.57/0.99      | k1_zfmisc_1(sK1) != X1
% 3.57/0.99      | sK2 != X0 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_299,plain,
% 3.57/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_298]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_21,plain,
% 3.57/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_305,plain,
% 3.57/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.57/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_299,c_21]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_605,plain,
% 3.57/0.99      ( r1_tarski(X0,X1) | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1) | sK2 != X0 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_474,c_305]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_606,plain,
% 3.57/0.99      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1049,plain,
% 3.57/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) | r1_tarski(sK2,X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1242,plain,
% 3.57/0.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_1049]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1058,plain,
% 3.57/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3261,plain,
% 3.57/0.99      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1242,c_1058]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2,plain,
% 3.57/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7645,plain,
% 3.57/0.99      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3261,c_2]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_20,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_311,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.57/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.57/0.99      | sK2 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_312,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 3.57/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_311]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1116,plain,
% 3.57/0.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_312]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7671,plain,
% 3.57/0.99      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7645,c_1116]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_23,negated_conjecture,
% 3.57/0.99      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 3.57/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1054,plain,
% 3.57/0.99      ( k2_subset_1(sK1) = sK2
% 3.57/0.99      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_19,plain,
% 3.57/0.99      ( k2_subset_1(X0) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1062,plain,
% 3.57/0.99      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_1054,c_19]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3258,plain,
% 3.57/0.99      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
% 3.57/0.99      | sK2 = sK1 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1062,c_1058]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9,plain,
% 3.57/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1056,plain,
% 3.57/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2670,plain,
% 3.57/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2,c_1056]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3538,plain,
% 3.57/0.99      ( sK2 = sK1
% 3.57/0.99      | r1_tarski(k5_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3258,c_2670]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3772,plain,
% 3.57/0.99      ( k3_xboole_0(k5_xboole_0(sK2,k3_subset_1(sK1,sK2)),sK2) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 3.57/0.99      | sK2 = sK1 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3538,c_1058]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7785,plain,
% 3.57/0.99      ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
% 3.57/0.99      | sK2 = sK1 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7671,c_3772]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.57/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1503,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4189,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2,c_1503]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7643,plain,
% 3.57/0.99      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3261,c_4189]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7646,plain,
% 3.57/0.99      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7643,c_7645]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10,plain,
% 3.57/0.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1061,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_6,c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f69]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1059,plain,
% 3.57/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_17,plain,
% 3.57/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_278,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | v1_xboole_0(X1)
% 3.57/0.99      | X2 != X0
% 3.57/0.99      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 3.57/0.99      | k1_zfmisc_1(X3) != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_279,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.57/0.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.57/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_278]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_289,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.57/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_279,c_21]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_13,plain,
% 3.57/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_475,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.57/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_476,plain,
% 3.57/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_475]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_514,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1)
% 3.57/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/0.99      inference(bin_hyper_res,[status(thm)],[c_289,c_476]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1053,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.57/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2544,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1059,c_1053]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_0,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1433,plain,
% 3.57/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2160,plain,
% 3.57/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1433,c_2]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2558,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2160,c_0]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2563,plain,
% 3.57/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_2558,c_2160]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2564,plain,
% 3.57/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_2563,c_1061,c_2544]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3255,plain,
% 3.57/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1059,c_1058]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5222,plain,
% 3.57/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.57/0.99      inference(light_normalisation,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_2544,c_2544,c_2564,c_3255]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7647,plain,
% 3.57/0.99      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7646,c_1061,c_5222]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7816,plain,
% 3.57/0.99      ( sK2 = sK1 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_7785,c_7645,c_7647]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_22,negated_conjecture,
% 3.57/0.99      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 3.57/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1055,plain,
% 3.57/0.99      ( k2_subset_1(sK1) != sK2
% 3.57/0.99      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1063,plain,
% 3.57/0.99      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_1055,c_19]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7809,plain,
% 3.57/0.99      ( sK2 != sK1 | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7671,c_1063]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7835,plain,
% 3.57/0.99      ( sK1 != sK1 | r1_tarski(k5_xboole_0(sK1,sK1),sK1) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7816,c_7809]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7836,plain,
% 3.57/0.99      ( r1_tarski(k5_xboole_0(sK1,sK1),sK1) != iProver_top ),
% 3.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_7835]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7837,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_7836,c_5222]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7954,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1057,c_7837]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.007
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.01
% 3.57/0.99  total_time:                             0.221
% 3.57/0.99  num_of_symbols:                         44
% 3.57/0.99  num_of_terms:                           5343
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    6
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       120
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        24
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        1
% 3.57/0.99  pred_elim:                              3
% 3.57/0.99  pred_elim_cl:                           5
% 3.57/0.99  pred_elim_cycles:                       6
% 3.57/0.99  merged_defs:                            14
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          15
% 3.57/0.99  prep_cycles:                            5
% 3.57/0.99  pred_elim_time:                         0.003
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                19
% 3.57/0.99  conjectures:                            2
% 3.57/0.99  epr:                                    3
% 3.57/0.99  horn:                                   17
% 3.57/0.99  ground:                                 2
% 3.57/0.99  unary:                                  9
% 3.57/0.99  binary:                                 6
% 3.57/0.99  lits:                                   33
% 3.57/0.99  lits_eq:                                18
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                0
% 3.57/0.99  fd_pseudo_cond:                         1
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      37
% 3.57/0.99  prop_fast_solver_calls:                 740
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    2985
% 3.57/0.99  prop_preprocess_simplified:             6000
% 3.57/0.99  prop_fo_subsumed:                       1
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    1026
% 3.57/0.99  inst_num_in_passive:                    80
% 3.57/0.99  inst_num_in_active:                     495
% 3.57/0.99  inst_num_in_unprocessed:                451
% 3.57/0.99  inst_num_of_loops:                      670
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          170
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                0
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      290
% 3.57/0.99  inst_num_of_non_proper_insts:           913
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       125
% 3.57/0.99  res_forward_subset_subsumed:            238
% 3.57/0.99  res_backward_subset_subsumed:           0
% 3.57/0.99  res_forward_subsumed:                   2
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     2
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       893
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      129
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     200
% 3.57/0.99  sup_num_in_active:                      36
% 3.57/0.99  sup_num_in_passive:                     164
% 3.57/0.99  sup_num_of_loops:                       133
% 3.57/0.99  sup_fw_superposition:                   373
% 3.57/0.99  sup_bw_superposition:                   351
% 3.57/0.99  sup_immediate_simplified:               232
% 3.57/0.99  sup_given_eliminated:                   2
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    142
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 31
% 3.57/0.99  sim_bw_subset_subsumed:                 12
% 3.57/0.99  sim_fw_subsumed:                        25
% 3.57/0.99  sim_bw_subsumed:                        7
% 3.57/0.99  sim_fw_subsumption_res:                 0
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      2
% 3.57/0.99  sim_eq_tautology_del:                   89
% 3.57/0.99  sim_eq_res_simp:                        1
% 3.57/0.99  sim_fw_demodulated:                     92
% 3.57/0.99  sim_bw_demodulated:                     120
% 3.57/0.99  sim_light_normalised:                   111
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------
