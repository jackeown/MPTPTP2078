%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:52 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 316 expanded)
%              Number of clauses        :   72 ( 150 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 ( 914 expanded)
%              Number of equality atoms :  149 ( 424 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f34,f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f51,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_693,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_694,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_693])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_299,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_300,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_306,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_300,c_16])).

cnf(c_812,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_694,c_306])).

cnf(c_813,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_941,plain,
    ( r1_tarski(sK2,X0_41)
    | k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1) ),
    inference(subtyping,[status(esa)],[c_813])).

cnf(c_1256,plain,
    ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_1443,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1256])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_951,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1247,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = X0_41
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_1997,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_1443,c_1247])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_952,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 != X2
    | k4_xboole_0(X3,X1) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_261,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_947,plain,
    ( ~ r1_tarski(k4_xboole_0(X0_41,X1_41),X1_41)
    | k1_xboole_0 = k4_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_1251,plain,
    ( k1_xboole_0 = k4_xboole_0(X0_41,X1_41)
    | r1_tarski(k4_xboole_0(X0_41,X1_41),X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_2001,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)),k4_xboole_0(X0_41,X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_1251])).

cnf(c_2757,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1997,c_2001])).

cnf(c_955,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_972,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_956,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1330,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_313,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_946,plain,
    ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1)
    | k3_subset_1(X0_41,sK2) = k4_xboole_0(X0_41,sK2) ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_1332,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_1342,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_946])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_948,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1250,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_1372,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1342,c_1250])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_949,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1249,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_1373,plain,
    ( sK2 != k1_xboole_0
    | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1342,c_1249])).

cnf(c_961,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_1394,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(k1_xboole_0,X2_41)
    | X1_41 != X2_41
    | X0_41 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_1509,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,X0_41)
    | k3_subset_1(sK1,sK2) != X0_41
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1538,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_1540,plain,
    ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != k1_xboole_0
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_1539,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_950,plain,
    ( r1_tarski(k1_xboole_0,X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1787,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1788,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_1389,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | X1_41 != k3_subset_1(sK1,sK2)
    | X0_41 != sK2 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_1808,plain,
    ( r1_tarski(X0_41,k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | X0_41 != sK2
    | k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_1809,plain,
    ( X0_41 != sK2
    | k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2)
    | r1_tarski(X0_41,k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_1811,plain,
    ( k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_959,plain,
    ( X0_41 != X1_41
    | k4_xboole_0(X2_41,X0_41) = k4_xboole_0(X2_41,X1_41) ),
    theory(equality)).

cnf(c_2520,plain,
    ( X0_41 != sK2
    | k4_xboole_0(sK1,X0_41) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_2521,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_957,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1694,plain,
    ( X0_41 != X1_41
    | k4_xboole_0(X2_41,X3_41) != X1_41
    | k4_xboole_0(X2_41,X3_41) = X0_41 ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_2090,plain,
    ( X0_41 != k4_xboole_0(X1_41,X2_41)
    | k4_xboole_0(X1_41,X3_41) = X0_41
    | k4_xboole_0(X1_41,X3_41) != k4_xboole_0(X1_41,X2_41) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_3691,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,X0_41)
    | k4_xboole_0(sK1,X1_41) = k3_subset_1(sK1,sK2)
    | k4_xboole_0(sK1,X1_41) != k4_xboole_0(sK1,X0_41) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_3692,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = k3_subset_1(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3691])).

cnf(c_6395,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_972,c_1330,c_1332,c_1372,c_1373,c_1540,c_1539,c_1788,c_1811,c_2521,c_3692])).

cnf(c_6474,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6395,c_952])).

cnf(c_6870,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6474,c_1997])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6870,c_3692,c_2521,c_1811,c_1788,c_1539,c_1540,c_1373,c_1332,c_1330,c_972])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.99/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/1.01  
% 2.99/1.01  ------  iProver source info
% 2.99/1.01  
% 2.99/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.99/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/1.01  git: non_committed_changes: false
% 2.99/1.01  git: last_make_outside_of_git: false
% 2.99/1.01  
% 2.99/1.01  ------ 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options
% 2.99/1.01  
% 2.99/1.01  --out_options                           all
% 2.99/1.01  --tptp_safe_out                         true
% 2.99/1.01  --problem_path                          ""
% 2.99/1.01  --include_path                          ""
% 2.99/1.01  --clausifier                            res/vclausify_rel
% 2.99/1.01  --clausifier_options                    --mode clausify
% 2.99/1.01  --stdin                                 false
% 2.99/1.01  --stats_out                             all
% 2.99/1.01  
% 2.99/1.01  ------ General Options
% 2.99/1.01  
% 2.99/1.01  --fof                                   false
% 2.99/1.01  --time_out_real                         305.
% 2.99/1.01  --time_out_virtual                      -1.
% 2.99/1.01  --symbol_type_check                     false
% 2.99/1.01  --clausify_out                          false
% 2.99/1.01  --sig_cnt_out                           false
% 2.99/1.01  --trig_cnt_out                          false
% 2.99/1.01  --trig_cnt_out_tolerance                1.
% 2.99/1.01  --trig_cnt_out_sk_spl                   false
% 2.99/1.01  --abstr_cl_out                          false
% 2.99/1.01  
% 2.99/1.01  ------ Global Options
% 2.99/1.01  
% 2.99/1.01  --schedule                              default
% 2.99/1.01  --add_important_lit                     false
% 2.99/1.01  --prop_solver_per_cl                    1000
% 2.99/1.01  --min_unsat_core                        false
% 2.99/1.01  --soft_assumptions                      false
% 2.99/1.01  --soft_lemma_size                       3
% 2.99/1.01  --prop_impl_unit_size                   0
% 2.99/1.01  --prop_impl_unit                        []
% 2.99/1.01  --share_sel_clauses                     true
% 2.99/1.01  --reset_solvers                         false
% 2.99/1.01  --bc_imp_inh                            [conj_cone]
% 2.99/1.01  --conj_cone_tolerance                   3.
% 2.99/1.01  --extra_neg_conj                        none
% 2.99/1.01  --large_theory_mode                     true
% 2.99/1.01  --prolific_symb_bound                   200
% 2.99/1.01  --lt_threshold                          2000
% 2.99/1.01  --clause_weak_htbl                      true
% 2.99/1.01  --gc_record_bc_elim                     false
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing Options
% 2.99/1.01  
% 2.99/1.01  --preprocessing_flag                    true
% 2.99/1.01  --time_out_prep_mult                    0.1
% 2.99/1.01  --splitting_mode                        input
% 2.99/1.01  --splitting_grd                         true
% 2.99/1.01  --splitting_cvd                         false
% 2.99/1.01  --splitting_cvd_svl                     false
% 2.99/1.01  --splitting_nvd                         32
% 2.99/1.01  --sub_typing                            true
% 2.99/1.01  --prep_gs_sim                           true
% 2.99/1.01  --prep_unflatten                        true
% 2.99/1.01  --prep_res_sim                          true
% 2.99/1.01  --prep_upred                            true
% 2.99/1.01  --prep_sem_filter                       exhaustive
% 2.99/1.01  --prep_sem_filter_out                   false
% 2.99/1.01  --pred_elim                             true
% 2.99/1.01  --res_sim_input                         true
% 2.99/1.01  --eq_ax_congr_red                       true
% 2.99/1.01  --pure_diseq_elim                       true
% 2.99/1.01  --brand_transform                       false
% 2.99/1.01  --non_eq_to_eq                          false
% 2.99/1.01  --prep_def_merge                        true
% 2.99/1.01  --prep_def_merge_prop_impl              false
% 2.99/1.01  --prep_def_merge_mbd                    true
% 2.99/1.01  --prep_def_merge_tr_red                 false
% 2.99/1.01  --prep_def_merge_tr_cl                  false
% 2.99/1.01  --smt_preprocessing                     true
% 2.99/1.01  --smt_ac_axioms                         fast
% 2.99/1.01  --preprocessed_out                      false
% 2.99/1.01  --preprocessed_stats                    false
% 2.99/1.01  
% 2.99/1.01  ------ Abstraction refinement Options
% 2.99/1.01  
% 2.99/1.01  --abstr_ref                             []
% 2.99/1.01  --abstr_ref_prep                        false
% 2.99/1.01  --abstr_ref_until_sat                   false
% 2.99/1.01  --abstr_ref_sig_restrict                funpre
% 2.99/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.01  --abstr_ref_under                       []
% 2.99/1.01  
% 2.99/1.01  ------ SAT Options
% 2.99/1.01  
% 2.99/1.01  --sat_mode                              false
% 2.99/1.01  --sat_fm_restart_options                ""
% 2.99/1.01  --sat_gr_def                            false
% 2.99/1.01  --sat_epr_types                         true
% 2.99/1.01  --sat_non_cyclic_types                  false
% 2.99/1.01  --sat_finite_models                     false
% 2.99/1.01  --sat_fm_lemmas                         false
% 2.99/1.01  --sat_fm_prep                           false
% 2.99/1.01  --sat_fm_uc_incr                        true
% 2.99/1.01  --sat_out_model                         small
% 2.99/1.01  --sat_out_clauses                       false
% 2.99/1.01  
% 2.99/1.01  ------ QBF Options
% 2.99/1.01  
% 2.99/1.01  --qbf_mode                              false
% 2.99/1.01  --qbf_elim_univ                         false
% 2.99/1.01  --qbf_dom_inst                          none
% 2.99/1.01  --qbf_dom_pre_inst                      false
% 2.99/1.01  --qbf_sk_in                             false
% 2.99/1.01  --qbf_pred_elim                         true
% 2.99/1.01  --qbf_split                             512
% 2.99/1.01  
% 2.99/1.01  ------ BMC1 Options
% 2.99/1.01  
% 2.99/1.01  --bmc1_incremental                      false
% 2.99/1.01  --bmc1_axioms                           reachable_all
% 2.99/1.01  --bmc1_min_bound                        0
% 2.99/1.01  --bmc1_max_bound                        -1
% 2.99/1.01  --bmc1_max_bound_default                -1
% 2.99/1.01  --bmc1_symbol_reachability              true
% 2.99/1.01  --bmc1_property_lemmas                  false
% 2.99/1.01  --bmc1_k_induction                      false
% 2.99/1.01  --bmc1_non_equiv_states                 false
% 2.99/1.01  --bmc1_deadlock                         false
% 2.99/1.01  --bmc1_ucm                              false
% 2.99/1.01  --bmc1_add_unsat_core                   none
% 2.99/1.01  --bmc1_unsat_core_children              false
% 2.99/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.01  --bmc1_out_stat                         full
% 2.99/1.01  --bmc1_ground_init                      false
% 2.99/1.01  --bmc1_pre_inst_next_state              false
% 2.99/1.01  --bmc1_pre_inst_state                   false
% 2.99/1.01  --bmc1_pre_inst_reach_state             false
% 2.99/1.01  --bmc1_out_unsat_core                   false
% 2.99/1.01  --bmc1_aig_witness_out                  false
% 2.99/1.01  --bmc1_verbose                          false
% 2.99/1.01  --bmc1_dump_clauses_tptp                false
% 2.99/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.01  --bmc1_dump_file                        -
% 2.99/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.01  --bmc1_ucm_extend_mode                  1
% 2.99/1.01  --bmc1_ucm_init_mode                    2
% 2.99/1.01  --bmc1_ucm_cone_mode                    none
% 2.99/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.01  --bmc1_ucm_relax_model                  4
% 2.99/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.01  --bmc1_ucm_layered_model                none
% 2.99/1.01  --bmc1_ucm_max_lemma_size               10
% 2.99/1.01  
% 2.99/1.01  ------ AIG Options
% 2.99/1.01  
% 2.99/1.01  --aig_mode                              false
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation Options
% 2.99/1.01  
% 2.99/1.01  --instantiation_flag                    true
% 2.99/1.01  --inst_sos_flag                         false
% 2.99/1.01  --inst_sos_phase                        true
% 2.99/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel_side                     num_symb
% 2.99/1.01  --inst_solver_per_active                1400
% 2.99/1.01  --inst_solver_calls_frac                1.
% 2.99/1.01  --inst_passive_queue_type               priority_queues
% 2.99/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.01  --inst_passive_queues_freq              [25;2]
% 2.99/1.01  --inst_dismatching                      true
% 2.99/1.01  --inst_eager_unprocessed_to_passive     true
% 2.99/1.01  --inst_prop_sim_given                   true
% 2.99/1.01  --inst_prop_sim_new                     false
% 2.99/1.01  --inst_subs_new                         false
% 2.99/1.01  --inst_eq_res_simp                      false
% 2.99/1.01  --inst_subs_given                       false
% 2.99/1.01  --inst_orphan_elimination               true
% 2.99/1.01  --inst_learning_loop_flag               true
% 2.99/1.01  --inst_learning_start                   3000
% 2.99/1.01  --inst_learning_factor                  2
% 2.99/1.01  --inst_start_prop_sim_after_learn       3
% 2.99/1.01  --inst_sel_renew                        solver
% 2.99/1.01  --inst_lit_activity_flag                true
% 2.99/1.01  --inst_restr_to_given                   false
% 2.99/1.01  --inst_activity_threshold               500
% 2.99/1.01  --inst_out_proof                        true
% 2.99/1.01  
% 2.99/1.01  ------ Resolution Options
% 2.99/1.01  
% 2.99/1.01  --resolution_flag                       true
% 2.99/1.01  --res_lit_sel                           adaptive
% 2.99/1.01  --res_lit_sel_side                      none
% 2.99/1.01  --res_ordering                          kbo
% 2.99/1.01  --res_to_prop_solver                    active
% 2.99/1.01  --res_prop_simpl_new                    false
% 2.99/1.01  --res_prop_simpl_given                  true
% 2.99/1.01  --res_passive_queue_type                priority_queues
% 2.99/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.01  --res_passive_queues_freq               [15;5]
% 2.99/1.01  --res_forward_subs                      full
% 2.99/1.01  --res_backward_subs                     full
% 2.99/1.01  --res_forward_subs_resolution           true
% 2.99/1.01  --res_backward_subs_resolution          true
% 2.99/1.01  --res_orphan_elimination                true
% 2.99/1.01  --res_time_limit                        2.
% 2.99/1.01  --res_out_proof                         true
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Options
% 2.99/1.01  
% 2.99/1.01  --superposition_flag                    true
% 2.99/1.01  --sup_passive_queue_type                priority_queues
% 2.99/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.01  --demod_completeness_check              fast
% 2.99/1.01  --demod_use_ground                      true
% 2.99/1.01  --sup_to_prop_solver                    passive
% 2.99/1.01  --sup_prop_simpl_new                    true
% 2.99/1.01  --sup_prop_simpl_given                  true
% 2.99/1.01  --sup_fun_splitting                     false
% 2.99/1.01  --sup_smt_interval                      50000
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Simplification Setup
% 2.99/1.01  
% 2.99/1.01  --sup_indices_passive                   []
% 2.99/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_full_bw                           [BwDemod]
% 2.99/1.01  --sup_immed_triv                        [TrivRules]
% 2.99/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_immed_bw_main                     []
% 2.99/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.01  
% 2.99/1.01  ------ Combination Options
% 2.99/1.01  
% 2.99/1.01  --comb_res_mult                         3
% 2.99/1.01  --comb_sup_mult                         2
% 2.99/1.01  --comb_inst_mult                        10
% 2.99/1.01  
% 2.99/1.01  ------ Debug Options
% 2.99/1.01  
% 2.99/1.01  --dbg_backtrace                         false
% 2.99/1.01  --dbg_dump_prop_clauses                 false
% 2.99/1.01  --dbg_dump_prop_clauses_file            -
% 2.99/1.01  --dbg_out_stat                          false
% 2.99/1.01  ------ Parsing...
% 2.99/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/1.01  ------ Proving...
% 2.99/1.01  ------ Problem Properties 
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  clauses                                 13
% 2.99/1.01  conjectures                             2
% 2.99/1.01  EPR                                     1
% 2.99/1.01  Horn                                    11
% 2.99/1.01  unary                                   3
% 2.99/1.01  binary                                  7
% 2.99/1.01  lits                                    26
% 2.99/1.01  lits eq                                 14
% 2.99/1.01  fd_pure                                 0
% 2.99/1.01  fd_pseudo                               0
% 2.99/1.01  fd_cond                                 0
% 2.99/1.01  fd_pseudo_cond                          0
% 2.99/1.01  AC symbols                              0
% 2.99/1.01  
% 2.99/1.01  ------ Schedule dynamic 5 is on 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  ------ 
% 2.99/1.01  Current options:
% 2.99/1.01  ------ 
% 2.99/1.01  
% 2.99/1.01  ------ Input Options
% 2.99/1.01  
% 2.99/1.01  --out_options                           all
% 2.99/1.01  --tptp_safe_out                         true
% 2.99/1.01  --problem_path                          ""
% 2.99/1.01  --include_path                          ""
% 2.99/1.01  --clausifier                            res/vclausify_rel
% 2.99/1.01  --clausifier_options                    --mode clausify
% 2.99/1.01  --stdin                                 false
% 2.99/1.01  --stats_out                             all
% 2.99/1.01  
% 2.99/1.01  ------ General Options
% 2.99/1.01  
% 2.99/1.01  --fof                                   false
% 2.99/1.01  --time_out_real                         305.
% 2.99/1.01  --time_out_virtual                      -1.
% 2.99/1.01  --symbol_type_check                     false
% 2.99/1.01  --clausify_out                          false
% 2.99/1.01  --sig_cnt_out                           false
% 2.99/1.01  --trig_cnt_out                          false
% 2.99/1.01  --trig_cnt_out_tolerance                1.
% 2.99/1.01  --trig_cnt_out_sk_spl                   false
% 2.99/1.01  --abstr_cl_out                          false
% 2.99/1.01  
% 2.99/1.01  ------ Global Options
% 2.99/1.01  
% 2.99/1.01  --schedule                              default
% 2.99/1.01  --add_important_lit                     false
% 2.99/1.01  --prop_solver_per_cl                    1000
% 2.99/1.01  --min_unsat_core                        false
% 2.99/1.01  --soft_assumptions                      false
% 2.99/1.01  --soft_lemma_size                       3
% 2.99/1.01  --prop_impl_unit_size                   0
% 2.99/1.01  --prop_impl_unit                        []
% 2.99/1.01  --share_sel_clauses                     true
% 2.99/1.01  --reset_solvers                         false
% 2.99/1.01  --bc_imp_inh                            [conj_cone]
% 2.99/1.01  --conj_cone_tolerance                   3.
% 2.99/1.01  --extra_neg_conj                        none
% 2.99/1.01  --large_theory_mode                     true
% 2.99/1.01  --prolific_symb_bound                   200
% 2.99/1.01  --lt_threshold                          2000
% 2.99/1.01  --clause_weak_htbl                      true
% 2.99/1.01  --gc_record_bc_elim                     false
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing Options
% 2.99/1.01  
% 2.99/1.01  --preprocessing_flag                    true
% 2.99/1.01  --time_out_prep_mult                    0.1
% 2.99/1.01  --splitting_mode                        input
% 2.99/1.01  --splitting_grd                         true
% 2.99/1.01  --splitting_cvd                         false
% 2.99/1.01  --splitting_cvd_svl                     false
% 2.99/1.01  --splitting_nvd                         32
% 2.99/1.01  --sub_typing                            true
% 2.99/1.01  --prep_gs_sim                           true
% 2.99/1.01  --prep_unflatten                        true
% 2.99/1.01  --prep_res_sim                          true
% 2.99/1.01  --prep_upred                            true
% 2.99/1.01  --prep_sem_filter                       exhaustive
% 2.99/1.01  --prep_sem_filter_out                   false
% 2.99/1.01  --pred_elim                             true
% 2.99/1.01  --res_sim_input                         true
% 2.99/1.01  --eq_ax_congr_red                       true
% 2.99/1.01  --pure_diseq_elim                       true
% 2.99/1.01  --brand_transform                       false
% 2.99/1.01  --non_eq_to_eq                          false
% 2.99/1.01  --prep_def_merge                        true
% 2.99/1.01  --prep_def_merge_prop_impl              false
% 2.99/1.01  --prep_def_merge_mbd                    true
% 2.99/1.01  --prep_def_merge_tr_red                 false
% 2.99/1.01  --prep_def_merge_tr_cl                  false
% 2.99/1.01  --smt_preprocessing                     true
% 2.99/1.01  --smt_ac_axioms                         fast
% 2.99/1.01  --preprocessed_out                      false
% 2.99/1.01  --preprocessed_stats                    false
% 2.99/1.01  
% 2.99/1.01  ------ Abstraction refinement Options
% 2.99/1.01  
% 2.99/1.01  --abstr_ref                             []
% 2.99/1.01  --abstr_ref_prep                        false
% 2.99/1.01  --abstr_ref_until_sat                   false
% 2.99/1.01  --abstr_ref_sig_restrict                funpre
% 2.99/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/1.01  --abstr_ref_under                       []
% 2.99/1.01  
% 2.99/1.01  ------ SAT Options
% 2.99/1.01  
% 2.99/1.01  --sat_mode                              false
% 2.99/1.01  --sat_fm_restart_options                ""
% 2.99/1.01  --sat_gr_def                            false
% 2.99/1.01  --sat_epr_types                         true
% 2.99/1.01  --sat_non_cyclic_types                  false
% 2.99/1.01  --sat_finite_models                     false
% 2.99/1.01  --sat_fm_lemmas                         false
% 2.99/1.01  --sat_fm_prep                           false
% 2.99/1.01  --sat_fm_uc_incr                        true
% 2.99/1.01  --sat_out_model                         small
% 2.99/1.01  --sat_out_clauses                       false
% 2.99/1.01  
% 2.99/1.01  ------ QBF Options
% 2.99/1.01  
% 2.99/1.01  --qbf_mode                              false
% 2.99/1.01  --qbf_elim_univ                         false
% 2.99/1.01  --qbf_dom_inst                          none
% 2.99/1.01  --qbf_dom_pre_inst                      false
% 2.99/1.01  --qbf_sk_in                             false
% 2.99/1.01  --qbf_pred_elim                         true
% 2.99/1.01  --qbf_split                             512
% 2.99/1.01  
% 2.99/1.01  ------ BMC1 Options
% 2.99/1.01  
% 2.99/1.01  --bmc1_incremental                      false
% 2.99/1.01  --bmc1_axioms                           reachable_all
% 2.99/1.01  --bmc1_min_bound                        0
% 2.99/1.01  --bmc1_max_bound                        -1
% 2.99/1.01  --bmc1_max_bound_default                -1
% 2.99/1.01  --bmc1_symbol_reachability              true
% 2.99/1.01  --bmc1_property_lemmas                  false
% 2.99/1.01  --bmc1_k_induction                      false
% 2.99/1.01  --bmc1_non_equiv_states                 false
% 2.99/1.01  --bmc1_deadlock                         false
% 2.99/1.01  --bmc1_ucm                              false
% 2.99/1.01  --bmc1_add_unsat_core                   none
% 2.99/1.01  --bmc1_unsat_core_children              false
% 2.99/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/1.01  --bmc1_out_stat                         full
% 2.99/1.01  --bmc1_ground_init                      false
% 2.99/1.01  --bmc1_pre_inst_next_state              false
% 2.99/1.01  --bmc1_pre_inst_state                   false
% 2.99/1.01  --bmc1_pre_inst_reach_state             false
% 2.99/1.01  --bmc1_out_unsat_core                   false
% 2.99/1.01  --bmc1_aig_witness_out                  false
% 2.99/1.01  --bmc1_verbose                          false
% 2.99/1.01  --bmc1_dump_clauses_tptp                false
% 2.99/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.99/1.01  --bmc1_dump_file                        -
% 2.99/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.99/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.99/1.01  --bmc1_ucm_extend_mode                  1
% 2.99/1.01  --bmc1_ucm_init_mode                    2
% 2.99/1.01  --bmc1_ucm_cone_mode                    none
% 2.99/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.99/1.01  --bmc1_ucm_relax_model                  4
% 2.99/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.99/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/1.01  --bmc1_ucm_layered_model                none
% 2.99/1.01  --bmc1_ucm_max_lemma_size               10
% 2.99/1.01  
% 2.99/1.01  ------ AIG Options
% 2.99/1.01  
% 2.99/1.01  --aig_mode                              false
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation Options
% 2.99/1.01  
% 2.99/1.01  --instantiation_flag                    true
% 2.99/1.01  --inst_sos_flag                         false
% 2.99/1.01  --inst_sos_phase                        true
% 2.99/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/1.01  --inst_lit_sel_side                     none
% 2.99/1.01  --inst_solver_per_active                1400
% 2.99/1.01  --inst_solver_calls_frac                1.
% 2.99/1.01  --inst_passive_queue_type               priority_queues
% 2.99/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/1.01  --inst_passive_queues_freq              [25;2]
% 2.99/1.01  --inst_dismatching                      true
% 2.99/1.01  --inst_eager_unprocessed_to_passive     true
% 2.99/1.01  --inst_prop_sim_given                   true
% 2.99/1.01  --inst_prop_sim_new                     false
% 2.99/1.01  --inst_subs_new                         false
% 2.99/1.01  --inst_eq_res_simp                      false
% 2.99/1.01  --inst_subs_given                       false
% 2.99/1.01  --inst_orphan_elimination               true
% 2.99/1.01  --inst_learning_loop_flag               true
% 2.99/1.01  --inst_learning_start                   3000
% 2.99/1.01  --inst_learning_factor                  2
% 2.99/1.01  --inst_start_prop_sim_after_learn       3
% 2.99/1.01  --inst_sel_renew                        solver
% 2.99/1.01  --inst_lit_activity_flag                true
% 2.99/1.01  --inst_restr_to_given                   false
% 2.99/1.01  --inst_activity_threshold               500
% 2.99/1.01  --inst_out_proof                        true
% 2.99/1.01  
% 2.99/1.01  ------ Resolution Options
% 2.99/1.01  
% 2.99/1.01  --resolution_flag                       false
% 2.99/1.01  --res_lit_sel                           adaptive
% 2.99/1.01  --res_lit_sel_side                      none
% 2.99/1.01  --res_ordering                          kbo
% 2.99/1.01  --res_to_prop_solver                    active
% 2.99/1.01  --res_prop_simpl_new                    false
% 2.99/1.01  --res_prop_simpl_given                  true
% 2.99/1.01  --res_passive_queue_type                priority_queues
% 2.99/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/1.01  --res_passive_queues_freq               [15;5]
% 2.99/1.01  --res_forward_subs                      full
% 2.99/1.01  --res_backward_subs                     full
% 2.99/1.01  --res_forward_subs_resolution           true
% 2.99/1.01  --res_backward_subs_resolution          true
% 2.99/1.01  --res_orphan_elimination                true
% 2.99/1.01  --res_time_limit                        2.
% 2.99/1.01  --res_out_proof                         true
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Options
% 2.99/1.01  
% 2.99/1.01  --superposition_flag                    true
% 2.99/1.01  --sup_passive_queue_type                priority_queues
% 2.99/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.99/1.01  --demod_completeness_check              fast
% 2.99/1.01  --demod_use_ground                      true
% 2.99/1.01  --sup_to_prop_solver                    passive
% 2.99/1.01  --sup_prop_simpl_new                    true
% 2.99/1.01  --sup_prop_simpl_given                  true
% 2.99/1.01  --sup_fun_splitting                     false
% 2.99/1.01  --sup_smt_interval                      50000
% 2.99/1.01  
% 2.99/1.01  ------ Superposition Simplification Setup
% 2.99/1.01  
% 2.99/1.01  --sup_indices_passive                   []
% 2.99/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_full_bw                           [BwDemod]
% 2.99/1.01  --sup_immed_triv                        [TrivRules]
% 2.99/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_immed_bw_main                     []
% 2.99/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/1.01  
% 2.99/1.01  ------ Combination Options
% 2.99/1.01  
% 2.99/1.01  --comb_res_mult                         3
% 2.99/1.01  --comb_sup_mult                         2
% 2.99/1.01  --comb_inst_mult                        10
% 2.99/1.01  
% 2.99/1.01  ------ Debug Options
% 2.99/1.01  
% 2.99/1.01  --dbg_backtrace                         false
% 2.99/1.01  --dbg_dump_prop_clauses                 false
% 2.99/1.01  --dbg_dump_prop_clauses_file            -
% 2.99/1.01  --dbg_out_stat                          false
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  ------ Proving...
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  % SZS status Theorem for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  fof(f8,axiom,(
% 2.99/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f21,plain,(
% 2.99/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.99/1.01    inference(nnf_transformation,[],[f8])).
% 2.99/1.01  
% 2.99/1.01  fof(f22,plain,(
% 2.99/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.99/1.01    inference(rectify,[],[f21])).
% 2.99/1.01  
% 2.99/1.01  fof(f23,plain,(
% 2.99/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f24,plain,(
% 2.99/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.99/1.01  
% 2.99/1.01  fof(f38,plain,(
% 2.99/1.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.99/1.01    inference(cnf_transformation,[],[f24])).
% 2.99/1.01  
% 2.99/1.01  fof(f59,plain,(
% 2.99/1.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.99/1.01    inference(equality_resolution,[],[f38])).
% 2.99/1.01  
% 2.99/1.01  fof(f9,axiom,(
% 2.99/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f18,plain,(
% 2.99/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.99/1.01    inference(ennf_transformation,[],[f9])).
% 2.99/1.01  
% 2.99/1.01  fof(f25,plain,(
% 2.99/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.99/1.01    inference(nnf_transformation,[],[f18])).
% 2.99/1.01  
% 2.99/1.01  fof(f42,plain,(
% 2.99/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f25])).
% 2.99/1.01  
% 2.99/1.01  fof(f13,conjecture,(
% 2.99/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f14,negated_conjecture,(
% 2.99/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.99/1.01    inference(negated_conjecture,[],[f13])).
% 2.99/1.01  
% 2.99/1.01  fof(f20,plain,(
% 2.99/1.01    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/1.01    inference(ennf_transformation,[],[f14])).
% 2.99/1.01  
% 2.99/1.01  fof(f26,plain,(
% 2.99/1.01    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/1.01    inference(nnf_transformation,[],[f20])).
% 2.99/1.01  
% 2.99/1.01  fof(f27,plain,(
% 2.99/1.01    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/1.01    inference(flattening,[],[f26])).
% 2.99/1.01  
% 2.99/1.01  fof(f28,plain,(
% 2.99/1.01    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.99/1.01    introduced(choice_axiom,[])).
% 2.99/1.01  
% 2.99/1.01  fof(f29,plain,(
% 2.99/1.01    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).
% 2.99/1.01  
% 2.99/1.01  fof(f49,plain,(
% 2.99/1.01    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.99/1.01    inference(cnf_transformation,[],[f29])).
% 2.99/1.01  
% 2.99/1.01  fof(f12,axiom,(
% 2.99/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f48,plain,(
% 2.99/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.99/1.01    inference(cnf_transformation,[],[f12])).
% 2.99/1.01  
% 2.99/1.01  fof(f3,axiom,(
% 2.99/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f15,plain,(
% 2.99/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.99/1.01    inference(ennf_transformation,[],[f3])).
% 2.99/1.01  
% 2.99/1.01  fof(f32,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f15])).
% 2.99/1.01  
% 2.99/1.01  fof(f5,axiom,(
% 2.99/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f34,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.99/1.01    inference(cnf_transformation,[],[f5])).
% 2.99/1.01  
% 2.99/1.01  fof(f54,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(definition_unfolding,[],[f32,f34])).
% 2.99/1.01  
% 2.99/1.01  fof(f1,axiom,(
% 2.99/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f30,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f1])).
% 2.99/1.01  
% 2.99/1.01  fof(f53,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.99/1.01    inference(definition_unfolding,[],[f30,f34,f34])).
% 2.99/1.01  
% 2.99/1.01  fof(f6,axiom,(
% 2.99/1.01    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f16,plain,(
% 2.99/1.01    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.99/1.01    inference(ennf_transformation,[],[f6])).
% 2.99/1.01  
% 2.99/1.01  fof(f36,plain,(
% 2.99/1.01    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.99/1.01    inference(cnf_transformation,[],[f16])).
% 2.99/1.01  
% 2.99/1.01  fof(f7,axiom,(
% 2.99/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f17,plain,(
% 2.99/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.99/1.01    inference(ennf_transformation,[],[f7])).
% 2.99/1.01  
% 2.99/1.01  fof(f37,plain,(
% 2.99/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f17])).
% 2.99/1.01  
% 2.99/1.01  fof(f11,axiom,(
% 2.99/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f19,plain,(
% 2.99/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/1.01    inference(ennf_transformation,[],[f11])).
% 2.99/1.01  
% 2.99/1.01  fof(f47,plain,(
% 2.99/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.99/1.01    inference(cnf_transformation,[],[f19])).
% 2.99/1.01  
% 2.99/1.01  fof(f50,plain,(
% 2.99/1.01    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.99/1.01    inference(cnf_transformation,[],[f29])).
% 2.99/1.01  
% 2.99/1.01  fof(f10,axiom,(
% 2.99/1.01    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f46,plain,(
% 2.99/1.01    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f10])).
% 2.99/1.01  
% 2.99/1.01  fof(f56,plain,(
% 2.99/1.01    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.99/1.01    inference(definition_unfolding,[],[f50,f46])).
% 2.99/1.01  
% 2.99/1.01  fof(f51,plain,(
% 2.99/1.01    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.99/1.01    inference(cnf_transformation,[],[f29])).
% 2.99/1.01  
% 2.99/1.01  fof(f55,plain,(
% 2.99/1.01    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 2.99/1.01    inference(definition_unfolding,[],[f51,f46])).
% 2.99/1.01  
% 2.99/1.01  fof(f4,axiom,(
% 2.99/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.99/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/1.01  
% 2.99/1.01  fof(f33,plain,(
% 2.99/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.99/1.01    inference(cnf_transformation,[],[f4])).
% 2.99/1.01  
% 2.99/1.01  cnf(c_10,plain,
% 2.99/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_693,plain,
% 2.99/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.99/1.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_694,plain,
% 2.99/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.99/1.01      inference(renaming,[status(thm)],[c_693]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_14,plain,
% 2.99/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.99/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_19,negated_conjecture,
% 2.99/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 2.99/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_299,plain,
% 2.99/1.01      ( r2_hidden(X0,X1)
% 2.99/1.01      | v1_xboole_0(X1)
% 2.99/1.01      | k1_zfmisc_1(sK1) != X1
% 2.99/1.01      | sK2 != X0 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_300,plain,
% 2.99/1.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_299]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_16,plain,
% 2.99/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.99/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_306,plain,
% 2.99/1.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 2.99/1.01      inference(forward_subsumption_resolution,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_300,c_16]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_812,plain,
% 2.99/1.01      ( r1_tarski(X0,X1)
% 2.99/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 2.99/1.01      | sK2 != X0 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_694,c_306]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_813,plain,
% 2.99/1.01      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_812]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_941,plain,
% 2.99/1.01      ( r1_tarski(sK2,X0_41) | k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1) ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_813]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1256,plain,
% 2.99/1.01      ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1)
% 2.99/1.01      | r1_tarski(sK2,X0_41) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1443,plain,
% 2.99/1.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 2.99/1.01      inference(equality_resolution,[status(thm)],[c_1256]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2,plain,
% 2.99/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.99/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_951,plain,
% 2.99/1.01      ( ~ r1_tarski(X0_41,X1_41)
% 2.99/1.01      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = X0_41 ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1247,plain,
% 2.99/1.01      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = X0_41
% 2.99/1.01      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1997,plain,
% 2.99/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1443,c_1247]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1,plain,
% 2.99/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.99/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_952,plain,
% 2.99/1.01      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_4,plain,
% 2.99/1.01      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.99/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_6,plain,
% 2.99/1.01      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 2.99/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_260,plain,
% 2.99/1.01      ( ~ r1_tarski(X0,X1)
% 2.99/1.01      | X0 != X2
% 2.99/1.01      | k4_xboole_0(X3,X1) != X2
% 2.99/1.01      | k1_xboole_0 = X2 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_261,plain,
% 2.99/1.01      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
% 2.99/1.01      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_260]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_947,plain,
% 2.99/1.01      ( ~ r1_tarski(k4_xboole_0(X0_41,X1_41),X1_41)
% 2.99/1.01      | k1_xboole_0 = k4_xboole_0(X0_41,X1_41) ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_261]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1251,plain,
% 2.99/1.01      ( k1_xboole_0 = k4_xboole_0(X0_41,X1_41)
% 2.99/1.01      | r1_tarski(k4_xboole_0(X0_41,X1_41),X1_41) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2001,plain,
% 2.99/1.01      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k1_xboole_0
% 2.99/1.01      | r1_tarski(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)),k4_xboole_0(X0_41,X1_41)) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_952,c_1251]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2757,plain,
% 2.99/1.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 2.99/1.01      | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) != iProver_top ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_1997,c_2001]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_955,plain,( X0_41 = X0_41 ),theory(equality) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_972,plain,
% 2.99/1.01      ( sK2 = sK2 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_955]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_956,plain,( X0_42 = X0_42 ),theory(equality) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1330,plain,
% 2.99/1.01      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_956]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_15,plain,
% 2.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/1.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.99/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_312,plain,
% 2.99/1.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.99/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 2.99/1.01      | sK2 != X1 ),
% 2.99/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_313,plain,
% 2.99/1.01      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 2.99/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.99/1.01      inference(unflattening,[status(thm)],[c_312]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_946,plain,
% 2.99/1.01      ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(sK1)
% 2.99/1.01      | k3_subset_1(X0_41,sK2) = k4_xboole_0(X0_41,sK2) ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_313]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1332,plain,
% 2.99/1.01      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 2.99/1.01      | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_946]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1342,plain,
% 2.99/1.01      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 2.99/1.01      inference(equality_resolution,[status(thm)],[c_946]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_18,negated_conjecture,
% 2.99/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 2.99/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_948,negated_conjecture,
% 2.99/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1250,plain,
% 2.99/1.01      ( k1_xboole_0 = sK2
% 2.99/1.01      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1372,plain,
% 2.99/1.01      ( sK2 = k1_xboole_0
% 2.99/1.01      | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 2.99/1.01      inference(demodulation,[status(thm)],[c_1342,c_1250]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_17,negated_conjecture,
% 2.99/1.01      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 2.99/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_949,negated_conjecture,
% 2.99/1.01      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1249,plain,
% 2.99/1.01      ( k1_xboole_0 != sK2
% 2.99/1.01      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1373,plain,
% 2.99/1.01      ( sK2 != k1_xboole_0
% 2.99/1.01      | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) != iProver_top ),
% 2.99/1.01      inference(demodulation,[status(thm)],[c_1342,c_1249]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_961,plain,
% 2.99/1.01      ( ~ r1_tarski(X0_41,X1_41)
% 2.99/1.01      | r1_tarski(X2_41,X3_41)
% 2.99/1.01      | X2_41 != X0_41
% 2.99/1.01      | X3_41 != X1_41 ),
% 2.99/1.01      theory(equality) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1394,plain,
% 2.99/1.01      ( r1_tarski(X0_41,X1_41)
% 2.99/1.01      | ~ r1_tarski(k1_xboole_0,X2_41)
% 2.99/1.01      | X1_41 != X2_41
% 2.99/1.01      | X0_41 != k1_xboole_0 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_961]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1509,plain,
% 2.99/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.99/1.01      | ~ r1_tarski(k1_xboole_0,X0_41)
% 2.99/1.01      | k3_subset_1(sK1,sK2) != X0_41
% 2.99/1.01      | sK2 != k1_xboole_0 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_1394]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1538,plain,
% 2.99/1.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.99/1.01      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
% 2.99/1.01      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 2.99/1.01      | sK2 != k1_xboole_0 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_1509]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1540,plain,
% 2.99/1.01      ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 2.99/1.01      | sK2 != k1_xboole_0
% 2.99/1.01      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
% 2.99/1.01      | r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1539,plain,
% 2.99/1.01      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_955]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3,plain,
% 2.99/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.99/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_950,plain,
% 2.99/1.01      ( r1_tarski(k1_xboole_0,X0_41) ),
% 2.99/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1787,plain,
% 2.99/1.01      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_950]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1788,plain,
% 2.99/1.01      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) = iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1389,plain,
% 2.99/1.01      ( r1_tarski(X0_41,X1_41)
% 2.99/1.01      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.99/1.01      | X1_41 != k3_subset_1(sK1,sK2)
% 2.99/1.01      | X0_41 != sK2 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_961]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1808,plain,
% 2.99/1.01      ( r1_tarski(X0_41,k4_xboole_0(sK1,sK2))
% 2.99/1.01      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 2.99/1.01      | X0_41 != sK2
% 2.99/1.01      | k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_1389]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1809,plain,
% 2.99/1.01      ( X0_41 != sK2
% 2.99/1.01      | k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2)
% 2.99/1.01      | r1_tarski(X0_41,k4_xboole_0(sK1,sK2)) = iProver_top
% 2.99/1.01      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 2.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1811,plain,
% 2.99/1.01      ( k4_xboole_0(sK1,sK2) != k3_subset_1(sK1,sK2)
% 2.99/1.01      | sK2 != sK2
% 2.99/1.01      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top
% 2.99/1.01      | r1_tarski(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_1809]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_959,plain,
% 2.99/1.01      ( X0_41 != X1_41
% 2.99/1.01      | k4_xboole_0(X2_41,X0_41) = k4_xboole_0(X2_41,X1_41) ),
% 2.99/1.01      theory(equality) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2520,plain,
% 2.99/1.01      ( X0_41 != sK2 | k4_xboole_0(sK1,X0_41) = k4_xboole_0(sK1,sK2) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_959]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2521,plain,
% 2.99/1.01      ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) | sK2 != sK2 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_2520]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_957,plain,
% 2.99/1.01      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 2.99/1.01      theory(equality) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_1694,plain,
% 2.99/1.01      ( X0_41 != X1_41
% 2.99/1.01      | k4_xboole_0(X2_41,X3_41) != X1_41
% 2.99/1.01      | k4_xboole_0(X2_41,X3_41) = X0_41 ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_957]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_2090,plain,
% 2.99/1.01      ( X0_41 != k4_xboole_0(X1_41,X2_41)
% 2.99/1.01      | k4_xboole_0(X1_41,X3_41) = X0_41
% 2.99/1.01      | k4_xboole_0(X1_41,X3_41) != k4_xboole_0(X1_41,X2_41) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_1694]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3691,plain,
% 2.99/1.01      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,X0_41)
% 2.99/1.01      | k4_xboole_0(sK1,X1_41) = k3_subset_1(sK1,sK2)
% 2.99/1.01      | k4_xboole_0(sK1,X1_41) != k4_xboole_0(sK1,X0_41) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_2090]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_3692,plain,
% 2.99/1.01      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 2.99/1.01      | k4_xboole_0(sK1,sK2) = k3_subset_1(sK1,sK2)
% 2.99/1.01      | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 2.99/1.01      inference(instantiation,[status(thm)],[c_3691]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_6395,plain,
% 2.99/1.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 2.99/1.01      inference(global_propositional_subsumption,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_2757,c_972,c_1330,c_1332,c_1372,c_1373,c_1540,c_1539,
% 2.99/1.01                 c_1788,c_1811,c_2521,c_3692]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_6474,plain,
% 2.99/1.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 2.99/1.01      inference(superposition,[status(thm)],[c_6395,c_952]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(c_6870,plain,
% 2.99/1.01      ( sK2 = k1_xboole_0 ),
% 2.99/1.01      inference(demodulation,[status(thm)],[c_6474,c_1997]) ).
% 2.99/1.01  
% 2.99/1.01  cnf(contradiction,plain,
% 2.99/1.01      ( $false ),
% 2.99/1.01      inference(minisat,
% 2.99/1.01                [status(thm)],
% 2.99/1.01                [c_6870,c_3692,c_2521,c_1811,c_1788,c_1539,c_1540,c_1373,
% 2.99/1.01                 c_1332,c_1330,c_972]) ).
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/1.01  
% 2.99/1.01  ------                               Statistics
% 2.99/1.01  
% 2.99/1.01  ------ General
% 2.99/1.01  
% 2.99/1.01  abstr_ref_over_cycles:                  0
% 2.99/1.01  abstr_ref_under_cycles:                 0
% 2.99/1.01  gc_basic_clause_elim:                   0
% 2.99/1.01  forced_gc_time:                         0
% 2.99/1.01  parsing_time:                           0.014
% 2.99/1.01  unif_index_cands_time:                  0.
% 2.99/1.01  unif_index_add_time:                    0.
% 2.99/1.01  orderings_time:                         0.
% 2.99/1.01  out_proof_time:                         0.008
% 2.99/1.01  total_time:                             0.233
% 2.99/1.01  num_of_symbols:                         46
% 2.99/1.01  num_of_terms:                           6742
% 2.99/1.01  
% 2.99/1.01  ------ Preprocessing
% 2.99/1.01  
% 2.99/1.01  num_of_splits:                          0
% 2.99/1.01  num_of_split_atoms:                     0
% 2.99/1.01  num_of_reused_defs:                     0
% 2.99/1.01  num_eq_ax_congr_red:                    14
% 2.99/1.01  num_of_sem_filtered_clauses:            1
% 2.99/1.01  num_of_subtypes:                        2
% 2.99/1.01  monotx_restored_types:                  0
% 2.99/1.01  sat_num_of_epr_types:                   0
% 2.99/1.01  sat_num_of_non_cyclic_types:            0
% 2.99/1.01  sat_guarded_non_collapsed_types:        1
% 2.99/1.01  num_pure_diseq_elim:                    0
% 2.99/1.01  simp_replaced_by:                       0
% 2.99/1.01  res_preprocessed:                       94
% 2.99/1.01  prep_upred:                             0
% 2.99/1.01  prep_unflattend:                        52
% 2.99/1.01  smt_new_axioms:                         0
% 2.99/1.01  pred_elim_cands:                        1
% 2.99/1.01  pred_elim:                              4
% 2.99/1.01  pred_elim_cl:                           7
% 2.99/1.01  pred_elim_cycles:                       8
% 2.99/1.01  merged_defs:                            14
% 2.99/1.01  merged_defs_ncl:                        0
% 2.99/1.01  bin_hyper_res:                          15
% 2.99/1.01  prep_cycles:                            5
% 2.99/1.01  pred_elim_time:                         0.022
% 2.99/1.01  splitting_time:                         0.
% 2.99/1.01  sem_filter_time:                        0.
% 2.99/1.01  monotx_time:                            0.
% 2.99/1.01  subtype_inf_time:                       0.
% 2.99/1.01  
% 2.99/1.01  ------ Problem properties
% 2.99/1.01  
% 2.99/1.01  clauses:                                13
% 2.99/1.01  conjectures:                            2
% 2.99/1.01  epr:                                    1
% 2.99/1.01  horn:                                   11
% 2.99/1.01  ground:                                 2
% 2.99/1.01  unary:                                  3
% 2.99/1.01  binary:                                 7
% 2.99/1.01  lits:                                   26
% 2.99/1.01  lits_eq:                                14
% 2.99/1.01  fd_pure:                                0
% 2.99/1.01  fd_pseudo:                              0
% 2.99/1.01  fd_cond:                                0
% 2.99/1.01  fd_pseudo_cond:                         0
% 2.99/1.01  ac_symbols:                             0
% 2.99/1.01  
% 2.99/1.01  ------ Propositional Solver
% 2.99/1.01  
% 2.99/1.01  prop_solver_calls:                      35
% 2.99/1.01  prop_fast_solver_calls:                 628
% 2.99/1.01  smt_solver_calls:                       0
% 2.99/1.01  smt_fast_solver_calls:                  0
% 2.99/1.01  prop_num_of_clauses:                    2075
% 2.99/1.01  prop_preprocess_simplified:             4434
% 2.99/1.01  prop_fo_subsumed:                       17
% 2.99/1.01  prop_solver_time:                       0.
% 2.99/1.01  smt_solver_time:                        0.
% 2.99/1.01  smt_fast_solver_time:                   0.
% 2.99/1.01  prop_fast_solver_time:                  0.
% 2.99/1.01  prop_unsat_core_time:                   0.
% 2.99/1.01  
% 2.99/1.01  ------ QBF
% 2.99/1.01  
% 2.99/1.01  qbf_q_res:                              0
% 2.99/1.01  qbf_num_tautologies:                    0
% 2.99/1.01  qbf_prep_cycles:                        0
% 2.99/1.01  
% 2.99/1.01  ------ BMC1
% 2.99/1.01  
% 2.99/1.01  bmc1_current_bound:                     -1
% 2.99/1.01  bmc1_last_solved_bound:                 -1
% 2.99/1.01  bmc1_unsat_core_size:                   -1
% 2.99/1.01  bmc1_unsat_core_parents_size:           -1
% 2.99/1.01  bmc1_merge_next_fun:                    0
% 2.99/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.99/1.01  
% 2.99/1.01  ------ Instantiation
% 2.99/1.01  
% 2.99/1.01  inst_num_of_clauses:                    513
% 2.99/1.01  inst_num_in_passive:                    119
% 2.99/1.01  inst_num_in_active:                     293
% 2.99/1.01  inst_num_in_unprocessed:                101
% 2.99/1.01  inst_num_of_loops:                      370
% 2.99/1.01  inst_num_of_learning_restarts:          0
% 2.99/1.01  inst_num_moves_active_passive:          72
% 2.99/1.01  inst_lit_activity:                      0
% 2.99/1.01  inst_lit_activity_moves:                0
% 2.99/1.01  inst_num_tautologies:                   0
% 2.99/1.01  inst_num_prop_implied:                  0
% 2.99/1.01  inst_num_existing_simplified:           0
% 2.99/1.01  inst_num_eq_res_simplified:             0
% 2.99/1.01  inst_num_child_elim:                    0
% 2.99/1.01  inst_num_of_dismatching_blockings:      304
% 2.99/1.01  inst_num_of_non_proper_insts:           593
% 2.99/1.01  inst_num_of_duplicates:                 0
% 2.99/1.01  inst_inst_num_from_inst_to_res:         0
% 2.99/1.01  inst_dismatching_checking_time:         0.
% 2.99/1.01  
% 2.99/1.01  ------ Resolution
% 2.99/1.01  
% 2.99/1.01  res_num_of_clauses:                     0
% 2.99/1.01  res_num_in_passive:                     0
% 2.99/1.01  res_num_in_active:                      0
% 2.99/1.01  res_num_of_loops:                       99
% 2.99/1.01  res_forward_subset_subsumed:            91
% 2.99/1.01  res_backward_subset_subsumed:           0
% 2.99/1.01  res_forward_subsumed:                   2
% 2.99/1.01  res_backward_subsumed:                  1
% 2.99/1.01  res_forward_subsumption_resolution:     2
% 2.99/1.01  res_backward_subsumption_resolution:    2
% 2.99/1.01  res_clause_to_clause_subsumption:       2398
% 2.99/1.01  res_orphan_elimination:                 0
% 2.99/1.01  res_tautology_del:                      122
% 2.99/1.01  res_num_eq_res_simplified:              0
% 2.99/1.01  res_num_sel_changes:                    0
% 2.99/1.01  res_moves_from_active_to_pass:          0
% 2.99/1.01  
% 2.99/1.01  ------ Superposition
% 2.99/1.01  
% 2.99/1.01  sup_time_total:                         0.
% 2.99/1.01  sup_time_generating:                    0.
% 2.99/1.01  sup_time_sim_full:                      0.
% 2.99/1.01  sup_time_sim_immed:                     0.
% 2.99/1.01  
% 2.99/1.01  sup_num_of_clauses:                     318
% 2.99/1.01  sup_num_in_active:                      56
% 2.99/1.01  sup_num_in_passive:                     262
% 2.99/1.01  sup_num_of_loops:                       73
% 2.99/1.01  sup_fw_superposition:                   297
% 2.99/1.01  sup_bw_superposition:                   370
% 2.99/1.01  sup_immediate_simplified:               333
% 2.99/1.01  sup_given_eliminated:                   2
% 2.99/1.01  comparisons_done:                       0
% 2.99/1.01  comparisons_avoided:                    3
% 2.99/1.01  
% 2.99/1.01  ------ Simplifications
% 2.99/1.01  
% 2.99/1.01  
% 2.99/1.01  sim_fw_subset_subsumed:                 8
% 2.99/1.01  sim_bw_subset_subsumed:                 12
% 2.99/1.01  sim_fw_subsumed:                        25
% 2.99/1.01  sim_bw_subsumed:                        6
% 2.99/1.01  sim_fw_subsumption_res:                 0
% 2.99/1.01  sim_bw_subsumption_res:                 0
% 2.99/1.01  sim_tautology_del:                      2
% 2.99/1.01  sim_eq_tautology_del:                   39
% 2.99/1.01  sim_eq_res_simp:                        0
% 2.99/1.01  sim_fw_demodulated:                     102
% 2.99/1.01  sim_bw_demodulated:                     77
% 2.99/1.01  sim_light_normalised:                   247
% 2.99/1.01  sim_joinable_taut:                      0
% 2.99/1.01  sim_joinable_simp:                      0
% 2.99/1.01  sim_ac_normalised:                      0
% 2.99/1.01  sim_smt_subsumption:                    0
% 2.99/1.01  
%------------------------------------------------------------------------------
