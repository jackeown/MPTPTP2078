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
% DateTime   : Thu Dec  3 12:24:43 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 226 expanded)
%              Number of clauses        :   46 (  69 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  247 ( 559 expanded)
%              Number of equality atoms :   86 ( 152 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f53,f64,f52])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK3)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK2,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK2,X1)) )
      & v1_zfmisc_1(sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r1_tarski(sK2,sK3)
    & ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f36,f35])).

fof(f60,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f61,f52])).

fof(f62,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_892,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_889,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2063,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_889])).

cnf(c_2754,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_2063])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_229,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK2)
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_20])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | sK2 = X0 ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_884,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_2782,plain,
    ( k4_xboole_0(sK2,X0) = sK2
    | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_884])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_895,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_897,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2998,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_897])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_888,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1570,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_888])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_907,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12,c_13])).

cnf(c_1580,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1570,c_907])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_893,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2971,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1580,c_893])).

cnf(c_4335,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2998,c_2971])).

cnf(c_4362,plain,
    ( k4_xboole_0(sK2,X0) = sK2
    | k4_xboole_0(sK2,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2782,c_4335])).

cnf(c_1572,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = sK2
    | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_884])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_886,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1647,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_1572,c_886])).

cnf(c_4493,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0
    | k4_xboole_0(sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_4362,c_1647])).

cnf(c_4518,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4493,c_907])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1013,plain,
    ( r1_tarski(sK2,sK3)
    | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4687,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4518,c_17,c_1013])).

cnf(c_887,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4701,plain,
    ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4687,c_887])).

cnf(c_4769,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4701,c_1580])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.26  % Computer   : n019.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 18:22:07 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  % Running in FOF mode
% 3.17/0.84  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/0.84  
% 3.17/0.84  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.84  
% 3.17/0.84  ------  iProver source info
% 3.17/0.84  
% 3.17/0.84  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.84  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.84  git: non_committed_changes: false
% 3.17/0.84  git: last_make_outside_of_git: false
% 3.17/0.84  
% 3.17/0.84  ------ 
% 3.17/0.84  
% 3.17/0.84  ------ Input Options
% 3.17/0.84  
% 3.17/0.84  --out_options                           all
% 3.17/0.84  --tptp_safe_out                         true
% 3.17/0.84  --problem_path                          ""
% 3.17/0.84  --include_path                          ""
% 3.17/0.84  --clausifier                            res/vclausify_rel
% 3.17/0.84  --clausifier_options                    --mode clausify
% 3.17/0.84  --stdin                                 false
% 3.17/0.84  --stats_out                             all
% 3.17/0.84  
% 3.17/0.84  ------ General Options
% 3.17/0.84  
% 3.17/0.84  --fof                                   false
% 3.17/0.84  --time_out_real                         305.
% 3.17/0.84  --time_out_virtual                      -1.
% 3.17/0.84  --symbol_type_check                     false
% 3.17/0.84  --clausify_out                          false
% 3.17/0.84  --sig_cnt_out                           false
% 3.17/0.84  --trig_cnt_out                          false
% 3.17/0.84  --trig_cnt_out_tolerance                1.
% 3.17/0.84  --trig_cnt_out_sk_spl                   false
% 3.17/0.84  --abstr_cl_out                          false
% 3.17/0.84  
% 3.17/0.84  ------ Global Options
% 3.17/0.84  
% 3.17/0.84  --schedule                              default
% 3.17/0.84  --add_important_lit                     false
% 3.17/0.84  --prop_solver_per_cl                    1000
% 3.17/0.84  --min_unsat_core                        false
% 3.17/0.84  --soft_assumptions                      false
% 3.17/0.84  --soft_lemma_size                       3
% 3.17/0.84  --prop_impl_unit_size                   0
% 3.17/0.84  --prop_impl_unit                        []
% 3.17/0.84  --share_sel_clauses                     true
% 3.17/0.84  --reset_solvers                         false
% 3.17/0.84  --bc_imp_inh                            [conj_cone]
% 3.17/0.84  --conj_cone_tolerance                   3.
% 3.17/0.84  --extra_neg_conj                        none
% 3.17/0.84  --large_theory_mode                     true
% 3.17/0.84  --prolific_symb_bound                   200
% 3.17/0.84  --lt_threshold                          2000
% 3.17/0.84  --clause_weak_htbl                      true
% 3.17/0.84  --gc_record_bc_elim                     false
% 3.17/0.84  
% 3.17/0.84  ------ Preprocessing Options
% 3.17/0.84  
% 3.17/0.84  --preprocessing_flag                    true
% 3.17/0.84  --time_out_prep_mult                    0.1
% 3.17/0.84  --splitting_mode                        input
% 3.17/0.84  --splitting_grd                         true
% 3.17/0.84  --splitting_cvd                         false
% 3.17/0.84  --splitting_cvd_svl                     false
% 3.17/0.84  --splitting_nvd                         32
% 3.17/0.84  --sub_typing                            true
% 3.17/0.84  --prep_gs_sim                           true
% 3.17/0.84  --prep_unflatten                        true
% 3.17/0.84  --prep_res_sim                          true
% 3.17/0.84  --prep_upred                            true
% 3.17/0.84  --prep_sem_filter                       exhaustive
% 3.17/0.84  --prep_sem_filter_out                   false
% 3.17/0.84  --pred_elim                             true
% 3.17/0.84  --res_sim_input                         true
% 3.17/0.84  --eq_ax_congr_red                       true
% 3.17/0.84  --pure_diseq_elim                       true
% 3.17/0.84  --brand_transform                       false
% 3.17/0.84  --non_eq_to_eq                          false
% 3.17/0.84  --prep_def_merge                        true
% 3.17/0.84  --prep_def_merge_prop_impl              false
% 3.17/0.84  --prep_def_merge_mbd                    true
% 3.17/0.84  --prep_def_merge_tr_red                 false
% 3.17/0.84  --prep_def_merge_tr_cl                  false
% 3.17/0.84  --smt_preprocessing                     true
% 3.17/0.84  --smt_ac_axioms                         fast
% 3.17/0.84  --preprocessed_out                      false
% 3.17/0.84  --preprocessed_stats                    false
% 3.17/0.84  
% 3.17/0.84  ------ Abstraction refinement Options
% 3.17/0.84  
% 3.17/0.84  --abstr_ref                             []
% 3.17/0.84  --abstr_ref_prep                        false
% 3.17/0.84  --abstr_ref_until_sat                   false
% 3.17/0.84  --abstr_ref_sig_restrict                funpre
% 3.17/0.84  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.84  --abstr_ref_under                       []
% 3.17/0.84  
% 3.17/0.84  ------ SAT Options
% 3.17/0.84  
% 3.17/0.84  --sat_mode                              false
% 3.17/0.84  --sat_fm_restart_options                ""
% 3.17/0.84  --sat_gr_def                            false
% 3.17/0.84  --sat_epr_types                         true
% 3.17/0.84  --sat_non_cyclic_types                  false
% 3.17/0.84  --sat_finite_models                     false
% 3.17/0.84  --sat_fm_lemmas                         false
% 3.17/0.84  --sat_fm_prep                           false
% 3.17/0.84  --sat_fm_uc_incr                        true
% 3.17/0.84  --sat_out_model                         small
% 3.17/0.84  --sat_out_clauses                       false
% 3.17/0.84  
% 3.17/0.84  ------ QBF Options
% 3.17/0.84  
% 3.17/0.84  --qbf_mode                              false
% 3.17/0.84  --qbf_elim_univ                         false
% 3.17/0.84  --qbf_dom_inst                          none
% 3.17/0.84  --qbf_dom_pre_inst                      false
% 3.17/0.84  --qbf_sk_in                             false
% 3.17/0.84  --qbf_pred_elim                         true
% 3.17/0.84  --qbf_split                             512
% 3.17/0.84  
% 3.17/0.84  ------ BMC1 Options
% 3.17/0.84  
% 3.17/0.84  --bmc1_incremental                      false
% 3.17/0.84  --bmc1_axioms                           reachable_all
% 3.17/0.84  --bmc1_min_bound                        0
% 3.17/0.84  --bmc1_max_bound                        -1
% 3.17/0.84  --bmc1_max_bound_default                -1
% 3.17/0.84  --bmc1_symbol_reachability              true
% 3.17/0.84  --bmc1_property_lemmas                  false
% 3.17/0.84  --bmc1_k_induction                      false
% 3.17/0.84  --bmc1_non_equiv_states                 false
% 3.17/0.84  --bmc1_deadlock                         false
% 3.17/0.84  --bmc1_ucm                              false
% 3.17/0.84  --bmc1_add_unsat_core                   none
% 3.17/0.84  --bmc1_unsat_core_children              false
% 3.17/0.84  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.84  --bmc1_out_stat                         full
% 3.17/0.84  --bmc1_ground_init                      false
% 3.17/0.84  --bmc1_pre_inst_next_state              false
% 3.17/0.84  --bmc1_pre_inst_state                   false
% 3.17/0.84  --bmc1_pre_inst_reach_state             false
% 3.17/0.84  --bmc1_out_unsat_core                   false
% 3.17/0.84  --bmc1_aig_witness_out                  false
% 3.17/0.84  --bmc1_verbose                          false
% 3.17/0.84  --bmc1_dump_clauses_tptp                false
% 3.17/0.84  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.84  --bmc1_dump_file                        -
% 3.17/0.84  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.84  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.84  --bmc1_ucm_extend_mode                  1
% 3.17/0.84  --bmc1_ucm_init_mode                    2
% 3.17/0.84  --bmc1_ucm_cone_mode                    none
% 3.17/0.84  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.84  --bmc1_ucm_relax_model                  4
% 3.17/0.84  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.84  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.84  --bmc1_ucm_layered_model                none
% 3.17/0.84  --bmc1_ucm_max_lemma_size               10
% 3.17/0.84  
% 3.17/0.84  ------ AIG Options
% 3.17/0.84  
% 3.17/0.84  --aig_mode                              false
% 3.17/0.84  
% 3.17/0.84  ------ Instantiation Options
% 3.17/0.84  
% 3.17/0.84  --instantiation_flag                    true
% 3.17/0.84  --inst_sos_flag                         false
% 3.17/0.84  --inst_sos_phase                        true
% 3.17/0.84  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.84  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.84  --inst_lit_sel_side                     num_symb
% 3.17/0.84  --inst_solver_per_active                1400
% 3.17/0.84  --inst_solver_calls_frac                1.
% 3.17/0.84  --inst_passive_queue_type               priority_queues
% 3.17/0.84  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.84  --inst_passive_queues_freq              [25;2]
% 3.17/0.84  --inst_dismatching                      true
% 3.17/0.84  --inst_eager_unprocessed_to_passive     true
% 3.17/0.84  --inst_prop_sim_given                   true
% 3.17/0.84  --inst_prop_sim_new                     false
% 3.17/0.84  --inst_subs_new                         false
% 3.17/0.84  --inst_eq_res_simp                      false
% 3.17/0.84  --inst_subs_given                       false
% 3.17/0.84  --inst_orphan_elimination               true
% 3.17/0.84  --inst_learning_loop_flag               true
% 3.17/0.84  --inst_learning_start                   3000
% 3.17/0.84  --inst_learning_factor                  2
% 3.17/0.84  --inst_start_prop_sim_after_learn       3
% 3.17/0.84  --inst_sel_renew                        solver
% 3.17/0.84  --inst_lit_activity_flag                true
% 3.17/0.84  --inst_restr_to_given                   false
% 3.17/0.84  --inst_activity_threshold               500
% 3.17/0.84  --inst_out_proof                        true
% 3.17/0.84  
% 3.17/0.84  ------ Resolution Options
% 3.17/0.84  
% 3.17/0.84  --resolution_flag                       true
% 3.17/0.84  --res_lit_sel                           adaptive
% 3.17/0.84  --res_lit_sel_side                      none
% 3.17/0.84  --res_ordering                          kbo
% 3.17/0.84  --res_to_prop_solver                    active
% 3.17/0.84  --res_prop_simpl_new                    false
% 3.17/0.84  --res_prop_simpl_given                  true
% 3.17/0.84  --res_passive_queue_type                priority_queues
% 3.17/0.84  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.84  --res_passive_queues_freq               [15;5]
% 3.17/0.84  --res_forward_subs                      full
% 3.17/0.84  --res_backward_subs                     full
% 3.17/0.84  --res_forward_subs_resolution           true
% 3.17/0.84  --res_backward_subs_resolution          true
% 3.17/0.84  --res_orphan_elimination                true
% 3.17/0.84  --res_time_limit                        2.
% 3.17/0.84  --res_out_proof                         true
% 3.17/0.84  
% 3.17/0.84  ------ Superposition Options
% 3.17/0.84  
% 3.17/0.84  --superposition_flag                    true
% 3.17/0.84  --sup_passive_queue_type                priority_queues
% 3.17/0.84  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.84  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.84  --demod_completeness_check              fast
% 3.17/0.84  --demod_use_ground                      true
% 3.17/0.84  --sup_to_prop_solver                    passive
% 3.17/0.84  --sup_prop_simpl_new                    true
% 3.17/0.84  --sup_prop_simpl_given                  true
% 3.17/0.84  --sup_fun_splitting                     false
% 3.17/0.84  --sup_smt_interval                      50000
% 3.17/0.84  
% 3.17/0.84  ------ Superposition Simplification Setup
% 3.17/0.84  
% 3.17/0.84  --sup_indices_passive                   []
% 3.17/0.84  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.84  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_full_bw                           [BwDemod]
% 3.17/0.84  --sup_immed_triv                        [TrivRules]
% 3.17/0.84  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.84  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_immed_bw_main                     []
% 3.17/0.84  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.84  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.84  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.84  
% 3.17/0.84  ------ Combination Options
% 3.17/0.84  
% 3.17/0.84  --comb_res_mult                         3
% 3.17/0.84  --comb_sup_mult                         2
% 3.17/0.84  --comb_inst_mult                        10
% 3.17/0.84  
% 3.17/0.84  ------ Debug Options
% 3.17/0.84  
% 3.17/0.84  --dbg_backtrace                         false
% 3.17/0.84  --dbg_dump_prop_clauses                 false
% 3.17/0.84  --dbg_dump_prop_clauses_file            -
% 3.17/0.84  --dbg_out_stat                          false
% 3.17/0.84  ------ Parsing...
% 3.17/0.84  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/0.84  
% 3.17/0.84  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/0.84  
% 3.17/0.84  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/0.84  
% 3.17/0.84  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/0.84  ------ Proving...
% 3.17/0.84  ------ Problem Properties 
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  clauses                                 19
% 3.17/0.84  conjectures                             3
% 3.17/0.84  EPR                                     7
% 3.17/0.84  Horn                                    16
% 3.17/0.84  unary                                   9
% 3.17/0.84  binary                                  7
% 3.17/0.84  lits                                    32
% 3.17/0.84  lits eq                                 8
% 3.17/0.84  fd_pure                                 0
% 3.17/0.84  fd_pseudo                               0
% 3.17/0.84  fd_cond                                 1
% 3.17/0.84  fd_pseudo_cond                          1
% 3.17/0.84  AC symbols                              0
% 3.17/0.84  
% 3.17/0.84  ------ Schedule dynamic 5 is on 
% 3.17/0.84  
% 3.17/0.84  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  ------ 
% 3.17/0.84  Current options:
% 3.17/0.84  ------ 
% 3.17/0.84  
% 3.17/0.84  ------ Input Options
% 3.17/0.84  
% 3.17/0.84  --out_options                           all
% 3.17/0.84  --tptp_safe_out                         true
% 3.17/0.84  --problem_path                          ""
% 3.17/0.84  --include_path                          ""
% 3.17/0.84  --clausifier                            res/vclausify_rel
% 3.17/0.84  --clausifier_options                    --mode clausify
% 3.17/0.84  --stdin                                 false
% 3.17/0.84  --stats_out                             all
% 3.17/0.84  
% 3.17/0.84  ------ General Options
% 3.17/0.84  
% 3.17/0.84  --fof                                   false
% 3.17/0.84  --time_out_real                         305.
% 3.17/0.84  --time_out_virtual                      -1.
% 3.17/0.84  --symbol_type_check                     false
% 3.17/0.84  --clausify_out                          false
% 3.17/0.84  --sig_cnt_out                           false
% 3.17/0.84  --trig_cnt_out                          false
% 3.17/0.84  --trig_cnt_out_tolerance                1.
% 3.17/0.84  --trig_cnt_out_sk_spl                   false
% 3.17/0.84  --abstr_cl_out                          false
% 3.17/0.84  
% 3.17/0.84  ------ Global Options
% 3.17/0.84  
% 3.17/0.84  --schedule                              default
% 3.17/0.84  --add_important_lit                     false
% 3.17/0.84  --prop_solver_per_cl                    1000
% 3.17/0.84  --min_unsat_core                        false
% 3.17/0.84  --soft_assumptions                      false
% 3.17/0.84  --soft_lemma_size                       3
% 3.17/0.84  --prop_impl_unit_size                   0
% 3.17/0.84  --prop_impl_unit                        []
% 3.17/0.84  --share_sel_clauses                     true
% 3.17/0.84  --reset_solvers                         false
% 3.17/0.84  --bc_imp_inh                            [conj_cone]
% 3.17/0.84  --conj_cone_tolerance                   3.
% 3.17/0.84  --extra_neg_conj                        none
% 3.17/0.84  --large_theory_mode                     true
% 3.17/0.84  --prolific_symb_bound                   200
% 3.17/0.84  --lt_threshold                          2000
% 3.17/0.84  --clause_weak_htbl                      true
% 3.17/0.84  --gc_record_bc_elim                     false
% 3.17/0.84  
% 3.17/0.84  ------ Preprocessing Options
% 3.17/0.84  
% 3.17/0.84  --preprocessing_flag                    true
% 3.17/0.84  --time_out_prep_mult                    0.1
% 3.17/0.84  --splitting_mode                        input
% 3.17/0.84  --splitting_grd                         true
% 3.17/0.84  --splitting_cvd                         false
% 3.17/0.84  --splitting_cvd_svl                     false
% 3.17/0.84  --splitting_nvd                         32
% 3.17/0.84  --sub_typing                            true
% 3.17/0.84  --prep_gs_sim                           true
% 3.17/0.84  --prep_unflatten                        true
% 3.17/0.84  --prep_res_sim                          true
% 3.17/0.84  --prep_upred                            true
% 3.17/0.84  --prep_sem_filter                       exhaustive
% 3.17/0.84  --prep_sem_filter_out                   false
% 3.17/0.84  --pred_elim                             true
% 3.17/0.84  --res_sim_input                         true
% 3.17/0.84  --eq_ax_congr_red                       true
% 3.17/0.84  --pure_diseq_elim                       true
% 3.17/0.84  --brand_transform                       false
% 3.17/0.84  --non_eq_to_eq                          false
% 3.17/0.84  --prep_def_merge                        true
% 3.17/0.84  --prep_def_merge_prop_impl              false
% 3.17/0.84  --prep_def_merge_mbd                    true
% 3.17/0.84  --prep_def_merge_tr_red                 false
% 3.17/0.84  --prep_def_merge_tr_cl                  false
% 3.17/0.84  --smt_preprocessing                     true
% 3.17/0.84  --smt_ac_axioms                         fast
% 3.17/0.84  --preprocessed_out                      false
% 3.17/0.84  --preprocessed_stats                    false
% 3.17/0.84  
% 3.17/0.84  ------ Abstraction refinement Options
% 3.17/0.84  
% 3.17/0.84  --abstr_ref                             []
% 3.17/0.84  --abstr_ref_prep                        false
% 3.17/0.84  --abstr_ref_until_sat                   false
% 3.17/0.84  --abstr_ref_sig_restrict                funpre
% 3.17/0.84  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.84  --abstr_ref_under                       []
% 3.17/0.84  
% 3.17/0.84  ------ SAT Options
% 3.17/0.84  
% 3.17/0.84  --sat_mode                              false
% 3.17/0.84  --sat_fm_restart_options                ""
% 3.17/0.84  --sat_gr_def                            false
% 3.17/0.84  --sat_epr_types                         true
% 3.17/0.84  --sat_non_cyclic_types                  false
% 3.17/0.84  --sat_finite_models                     false
% 3.17/0.84  --sat_fm_lemmas                         false
% 3.17/0.84  --sat_fm_prep                           false
% 3.17/0.84  --sat_fm_uc_incr                        true
% 3.17/0.84  --sat_out_model                         small
% 3.17/0.84  --sat_out_clauses                       false
% 3.17/0.84  
% 3.17/0.84  ------ QBF Options
% 3.17/0.84  
% 3.17/0.84  --qbf_mode                              false
% 3.17/0.84  --qbf_elim_univ                         false
% 3.17/0.84  --qbf_dom_inst                          none
% 3.17/0.84  --qbf_dom_pre_inst                      false
% 3.17/0.84  --qbf_sk_in                             false
% 3.17/0.84  --qbf_pred_elim                         true
% 3.17/0.84  --qbf_split                             512
% 3.17/0.84  
% 3.17/0.84  ------ BMC1 Options
% 3.17/0.84  
% 3.17/0.84  --bmc1_incremental                      false
% 3.17/0.84  --bmc1_axioms                           reachable_all
% 3.17/0.84  --bmc1_min_bound                        0
% 3.17/0.84  --bmc1_max_bound                        -1
% 3.17/0.84  --bmc1_max_bound_default                -1
% 3.17/0.84  --bmc1_symbol_reachability              true
% 3.17/0.84  --bmc1_property_lemmas                  false
% 3.17/0.84  --bmc1_k_induction                      false
% 3.17/0.84  --bmc1_non_equiv_states                 false
% 3.17/0.84  --bmc1_deadlock                         false
% 3.17/0.84  --bmc1_ucm                              false
% 3.17/0.84  --bmc1_add_unsat_core                   none
% 3.17/0.84  --bmc1_unsat_core_children              false
% 3.17/0.84  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.84  --bmc1_out_stat                         full
% 3.17/0.84  --bmc1_ground_init                      false
% 3.17/0.84  --bmc1_pre_inst_next_state              false
% 3.17/0.84  --bmc1_pre_inst_state                   false
% 3.17/0.84  --bmc1_pre_inst_reach_state             false
% 3.17/0.84  --bmc1_out_unsat_core                   false
% 3.17/0.84  --bmc1_aig_witness_out                  false
% 3.17/0.84  --bmc1_verbose                          false
% 3.17/0.84  --bmc1_dump_clauses_tptp                false
% 3.17/0.84  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.84  --bmc1_dump_file                        -
% 3.17/0.84  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.84  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.84  --bmc1_ucm_extend_mode                  1
% 3.17/0.84  --bmc1_ucm_init_mode                    2
% 3.17/0.84  --bmc1_ucm_cone_mode                    none
% 3.17/0.84  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.84  --bmc1_ucm_relax_model                  4
% 3.17/0.84  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.84  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.84  --bmc1_ucm_layered_model                none
% 3.17/0.84  --bmc1_ucm_max_lemma_size               10
% 3.17/0.84  
% 3.17/0.84  ------ AIG Options
% 3.17/0.84  
% 3.17/0.84  --aig_mode                              false
% 3.17/0.84  
% 3.17/0.84  ------ Instantiation Options
% 3.17/0.84  
% 3.17/0.84  --instantiation_flag                    true
% 3.17/0.84  --inst_sos_flag                         false
% 3.17/0.84  --inst_sos_phase                        true
% 3.17/0.84  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.84  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.84  --inst_lit_sel_side                     none
% 3.17/0.84  --inst_solver_per_active                1400
% 3.17/0.84  --inst_solver_calls_frac                1.
% 3.17/0.84  --inst_passive_queue_type               priority_queues
% 3.17/0.84  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.84  --inst_passive_queues_freq              [25;2]
% 3.17/0.84  --inst_dismatching                      true
% 3.17/0.84  --inst_eager_unprocessed_to_passive     true
% 3.17/0.84  --inst_prop_sim_given                   true
% 3.17/0.84  --inst_prop_sim_new                     false
% 3.17/0.84  --inst_subs_new                         false
% 3.17/0.84  --inst_eq_res_simp                      false
% 3.17/0.84  --inst_subs_given                       false
% 3.17/0.84  --inst_orphan_elimination               true
% 3.17/0.84  --inst_learning_loop_flag               true
% 3.17/0.84  --inst_learning_start                   3000
% 3.17/0.84  --inst_learning_factor                  2
% 3.17/0.84  --inst_start_prop_sim_after_learn       3
% 3.17/0.84  --inst_sel_renew                        solver
% 3.17/0.84  --inst_lit_activity_flag                true
% 3.17/0.84  --inst_restr_to_given                   false
% 3.17/0.84  --inst_activity_threshold               500
% 3.17/0.84  --inst_out_proof                        true
% 3.17/0.84  
% 3.17/0.84  ------ Resolution Options
% 3.17/0.84  
% 3.17/0.84  --resolution_flag                       false
% 3.17/0.84  --res_lit_sel                           adaptive
% 3.17/0.84  --res_lit_sel_side                      none
% 3.17/0.84  --res_ordering                          kbo
% 3.17/0.84  --res_to_prop_solver                    active
% 3.17/0.84  --res_prop_simpl_new                    false
% 3.17/0.84  --res_prop_simpl_given                  true
% 3.17/0.84  --res_passive_queue_type                priority_queues
% 3.17/0.84  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.84  --res_passive_queues_freq               [15;5]
% 3.17/0.84  --res_forward_subs                      full
% 3.17/0.84  --res_backward_subs                     full
% 3.17/0.84  --res_forward_subs_resolution           true
% 3.17/0.84  --res_backward_subs_resolution          true
% 3.17/0.84  --res_orphan_elimination                true
% 3.17/0.84  --res_time_limit                        2.
% 3.17/0.84  --res_out_proof                         true
% 3.17/0.84  
% 3.17/0.84  ------ Superposition Options
% 3.17/0.84  
% 3.17/0.84  --superposition_flag                    true
% 3.17/0.84  --sup_passive_queue_type                priority_queues
% 3.17/0.84  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.84  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.84  --demod_completeness_check              fast
% 3.17/0.84  --demod_use_ground                      true
% 3.17/0.84  --sup_to_prop_solver                    passive
% 3.17/0.84  --sup_prop_simpl_new                    true
% 3.17/0.84  --sup_prop_simpl_given                  true
% 3.17/0.84  --sup_fun_splitting                     false
% 3.17/0.84  --sup_smt_interval                      50000
% 3.17/0.84  
% 3.17/0.84  ------ Superposition Simplification Setup
% 3.17/0.84  
% 3.17/0.84  --sup_indices_passive                   []
% 3.17/0.84  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.84  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.84  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_full_bw                           [BwDemod]
% 3.17/0.84  --sup_immed_triv                        [TrivRules]
% 3.17/0.84  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.84  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_immed_bw_main                     []
% 3.17/0.84  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.84  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.84  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.84  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.84  
% 3.17/0.84  ------ Combination Options
% 3.17/0.84  
% 3.17/0.84  --comb_res_mult                         3
% 3.17/0.84  --comb_sup_mult                         2
% 3.17/0.84  --comb_inst_mult                        10
% 3.17/0.84  
% 3.17/0.84  ------ Debug Options
% 3.17/0.84  
% 3.17/0.84  --dbg_backtrace                         false
% 3.17/0.84  --dbg_dump_prop_clauses                 false
% 3.17/0.84  --dbg_dump_prop_clauses_file            -
% 3.17/0.84  --dbg_out_stat                          false
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  ------ Proving...
% 3.17/0.84  
% 3.17/0.84  
% 3.17/0.84  % SZS status Theorem for theBenchmark.p
% 3.17/0.84  
% 3.17/0.84   Resolution empty clause
% 3.17/0.84  
% 3.17/0.84  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/0.84  
% 3.17/0.84  fof(f3,axiom,(
% 3.17/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f32,plain,(
% 3.17/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.17/0.84    inference(nnf_transformation,[],[f3])).
% 3.17/0.84  
% 3.17/0.84  fof(f33,plain,(
% 3.17/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.17/0.84    inference(flattening,[],[f32])).
% 3.17/0.84  
% 3.17/0.84  fof(f43,plain,(
% 3.17/0.84    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.17/0.84    inference(cnf_transformation,[],[f33])).
% 3.17/0.84  
% 3.17/0.84  fof(f72,plain,(
% 3.17/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.17/0.84    inference(equality_resolution,[],[f43])).
% 3.17/0.84  
% 3.17/0.84  fof(f10,axiom,(
% 3.17/0.84    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f53,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.17/0.84    inference(cnf_transformation,[],[f10])).
% 3.17/0.84  
% 3.17/0.84  fof(f13,axiom,(
% 3.17/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f56,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.17/0.84    inference(cnf_transformation,[],[f13])).
% 3.17/0.84  
% 3.17/0.84  fof(f11,axiom,(
% 3.17/0.84    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f54,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.17/0.84    inference(cnf_transformation,[],[f11])).
% 3.17/0.84  
% 3.17/0.84  fof(f12,axiom,(
% 3.17/0.84    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f55,plain,(
% 3.17/0.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.17/0.84    inference(cnf_transformation,[],[f12])).
% 3.17/0.84  
% 3.17/0.84  fof(f63,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.17/0.84    inference(definition_unfolding,[],[f54,f55])).
% 3.17/0.84  
% 3.17/0.84  fof(f64,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.17/0.84    inference(definition_unfolding,[],[f56,f63])).
% 3.17/0.84  
% 3.17/0.84  fof(f9,axiom,(
% 3.17/0.84    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f52,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.17/0.84    inference(cnf_transformation,[],[f9])).
% 3.17/0.84  
% 3.17/0.84  fof(f68,plain,(
% 3.17/0.84    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 3.17/0.84    inference(definition_unfolding,[],[f53,f64,f52])).
% 3.17/0.84  
% 3.17/0.84  fof(f5,axiom,(
% 3.17/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f19,plain,(
% 3.17/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.17/0.84    inference(ennf_transformation,[],[f5])).
% 3.17/0.84  
% 3.17/0.84  fof(f48,plain,(
% 3.17/0.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.17/0.84    inference(cnf_transformation,[],[f19])).
% 3.17/0.84  
% 3.17/0.84  fof(f65,plain,(
% 3.17/0.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.17/0.84    inference(definition_unfolding,[],[f48,f64])).
% 3.17/0.84  
% 3.17/0.84  fof(f15,axiom,(
% 3.17/0.84    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f20,plain,(
% 3.17/0.84    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.17/0.84    inference(ennf_transformation,[],[f15])).
% 3.17/0.84  
% 3.17/0.84  fof(f21,plain,(
% 3.17/0.84    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.17/0.84    inference(flattening,[],[f20])).
% 3.17/0.84  
% 3.17/0.84  fof(f58,plain,(
% 3.17/0.84    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.17/0.84    inference(cnf_transformation,[],[f21])).
% 3.17/0.84  
% 3.17/0.84  fof(f16,conjecture,(
% 3.17/0.84    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.17/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.84  
% 3.17/0.84  fof(f17,negated_conjecture,(
% 3.17/0.84    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.17/0.84    inference(negated_conjecture,[],[f16])).
% 3.17/0.84  
% 3.17/0.84  fof(f22,plain,(
% 3.17/0.84    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 3.17/0.84    inference(ennf_transformation,[],[f17])).
% 3.17/0.84  
% 3.17/0.84  fof(f23,plain,(
% 3.17/0.84    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 3.17/0.84    inference(flattening,[],[f22])).
% 3.17/0.84  
% 3.17/0.84  fof(f36,plain,(
% 3.17/0.84    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK3) & ~v1_xboole_0(k3_xboole_0(X0,sK3)))) )),
% 3.17/0.84    introduced(choice_axiom,[])).
% 3.17/0.84  
% 3.17/0.84  fof(f35,plain,(
% 3.17/0.84    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK2,X1) & ~v1_xboole_0(k3_xboole_0(sK2,X1))) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2))),
% 3.17/0.85    introduced(choice_axiom,[])).
% 3.17/0.85  
% 3.17/0.85  fof(f37,plain,(
% 3.17/0.85    (~r1_tarski(sK2,sK3) & ~v1_xboole_0(k3_xboole_0(sK2,sK3))) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2)),
% 3.17/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f36,f35])).
% 3.17/0.85  
% 3.17/0.85  fof(f60,plain,(
% 3.17/0.85    v1_zfmisc_1(sK2)),
% 3.17/0.85    inference(cnf_transformation,[],[f37])).
% 3.17/0.85  
% 3.17/0.85  fof(f59,plain,(
% 3.17/0.85    ~v1_xboole_0(sK2)),
% 3.17/0.85    inference(cnf_transformation,[],[f37])).
% 3.17/0.85  
% 3.17/0.85  fof(f2,axiom,(
% 3.17/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f18,plain,(
% 3.17/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.17/0.85    inference(ennf_transformation,[],[f2])).
% 3.17/0.85  
% 3.17/0.85  fof(f28,plain,(
% 3.17/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.85    inference(nnf_transformation,[],[f18])).
% 3.17/0.85  
% 3.17/0.85  fof(f29,plain,(
% 3.17/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.85    inference(rectify,[],[f28])).
% 3.17/0.85  
% 3.17/0.85  fof(f30,plain,(
% 3.17/0.85    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.17/0.85    introduced(choice_axiom,[])).
% 3.17/0.85  
% 3.17/0.85  fof(f31,plain,(
% 3.17/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.17/0.85  
% 3.17/0.85  fof(f41,plain,(
% 3.17/0.85    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.17/0.85    inference(cnf_transformation,[],[f31])).
% 3.17/0.85  
% 3.17/0.85  fof(f1,axiom,(
% 3.17/0.85    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f24,plain,(
% 3.17/0.85    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.85    inference(nnf_transformation,[],[f1])).
% 3.17/0.85  
% 3.17/0.85  fof(f25,plain,(
% 3.17/0.85    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.85    inference(rectify,[],[f24])).
% 3.17/0.85  
% 3.17/0.85  fof(f26,plain,(
% 3.17/0.85    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.17/0.85    introduced(choice_axiom,[])).
% 3.17/0.85  
% 3.17/0.85  fof(f27,plain,(
% 3.17/0.85    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.17/0.85  
% 3.17/0.85  fof(f38,plain,(
% 3.17/0.85    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.17/0.85    inference(cnf_transformation,[],[f27])).
% 3.17/0.85  
% 3.17/0.85  fof(f8,axiom,(
% 3.17/0.85    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f51,plain,(
% 3.17/0.85    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.17/0.85    inference(cnf_transformation,[],[f8])).
% 3.17/0.85  
% 3.17/0.85  fof(f6,axiom,(
% 3.17/0.85    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f49,plain,(
% 3.17/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.17/0.85    inference(cnf_transformation,[],[f6])).
% 3.17/0.85  
% 3.17/0.85  fof(f66,plain,(
% 3.17/0.85    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.17/0.85    inference(definition_unfolding,[],[f49,f52])).
% 3.17/0.85  
% 3.17/0.85  fof(f7,axiom,(
% 3.17/0.85    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f50,plain,(
% 3.17/0.85    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.17/0.85    inference(cnf_transformation,[],[f7])).
% 3.17/0.85  
% 3.17/0.85  fof(f67,plain,(
% 3.17/0.85    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.17/0.85    inference(definition_unfolding,[],[f50,f52])).
% 3.17/0.85  
% 3.17/0.85  fof(f45,plain,(
% 3.17/0.85    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.17/0.85    inference(cnf_transformation,[],[f33])).
% 3.17/0.85  
% 3.17/0.85  fof(f61,plain,(
% 3.17/0.85    ~v1_xboole_0(k3_xboole_0(sK2,sK3))),
% 3.17/0.85    inference(cnf_transformation,[],[f37])).
% 3.17/0.85  
% 3.17/0.85  fof(f70,plain,(
% 3.17/0.85    ~v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 3.17/0.85    inference(definition_unfolding,[],[f61,f52])).
% 3.17/0.85  
% 3.17/0.85  fof(f62,plain,(
% 3.17/0.85    ~r1_tarski(sK2,sK3)),
% 3.17/0.85    inference(cnf_transformation,[],[f37])).
% 3.17/0.85  
% 3.17/0.85  fof(f4,axiom,(
% 3.17/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.17/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.85  
% 3.17/0.85  fof(f34,plain,(
% 3.17/0.85    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.17/0.85    inference(nnf_transformation,[],[f4])).
% 3.17/0.85  
% 3.17/0.85  fof(f46,plain,(
% 3.17/0.85    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.17/0.85    inference(cnf_transformation,[],[f34])).
% 3.17/0.85  
% 3.17/0.85  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_892,plain,
% 3.17/0.85      ( r1_tarski(X0,X0) = iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_14,plain,
% 3.17/0.85      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f68]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_10,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,X1)
% 3.17/0.85      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 3.17/0.85      inference(cnf_transformation,[],[f65]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_889,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) != iProver_top
% 3.17/0.85      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_2063,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) = iProver_top
% 3.17/0.85      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_14,c_889]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_2754,plain,
% 3.17/0.85      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_892,c_2063]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_16,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,X1)
% 3.17/0.85      | ~ v1_zfmisc_1(X1)
% 3.17/0.85      | v1_xboole_0(X0)
% 3.17/0.85      | v1_xboole_0(X1)
% 3.17/0.85      | X1 = X0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f58]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_19,negated_conjecture,
% 3.17/0.85      ( v1_zfmisc_1(sK2) ),
% 3.17/0.85      inference(cnf_transformation,[],[f60]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_224,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,X1)
% 3.17/0.85      | v1_xboole_0(X0)
% 3.17/0.85      | v1_xboole_0(X1)
% 3.17/0.85      | X1 = X0
% 3.17/0.85      | sK2 != X1 ),
% 3.17/0.85      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_225,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 = X0 ),
% 3.17/0.85      inference(unflattening,[status(thm)],[c_224]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_20,negated_conjecture,
% 3.17/0.85      ( ~ v1_xboole_0(sK2) ),
% 3.17/0.85      inference(cnf_transformation,[],[f59]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_229,plain,
% 3.17/0.85      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK2) | sK2 = X0 ),
% 3.17/0.85      inference(global_propositional_subsumption,[status(thm)],[c_225,c_20]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_230,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | sK2 = X0 ),
% 3.17/0.85      inference(renaming,[status(thm)],[c_229]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_884,plain,
% 3.17/0.85      ( sK2 = X0
% 3.17/0.85      | r1_tarski(X0,sK2) != iProver_top
% 3.17/0.85      | v1_xboole_0(X0) = iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_2782,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,X0) = sK2
% 3.17/0.85      | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_2754,c_884]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_3,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.17/0.85      inference(cnf_transformation,[],[f41]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_895,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) = iProver_top
% 3.17/0.85      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1,plain,
% 3.17/0.85      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.17/0.85      inference(cnf_transformation,[],[f38]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_897,plain,
% 3.17/0.85      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_2998,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_895,c_897]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_13,plain,
% 3.17/0.85      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f51]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_11,plain,
% 3.17/0.85      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.17/0.85      inference(cnf_transformation,[],[f66]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_888,plain,
% 3.17/0.85      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1570,plain,
% 3.17/0.85      ( r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_13,c_888]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_12,plain,
% 3.17/0.85      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f67]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_907,plain,
% 3.17/0.85      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.17/0.85      inference(light_normalisation,[status(thm)],[c_12,c_13]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1580,plain,
% 3.17/0.85      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.17/0.85      inference(light_normalisation,[status(thm)],[c_1570,c_907]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_5,plain,
% 3.17/0.85      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f45]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_893,plain,
% 3.17/0.85      ( X0 = X1
% 3.17/0.85      | r1_tarski(X1,X0) != iProver_top
% 3.17/0.85      | r1_tarski(X0,X1) != iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_2971,plain,
% 3.17/0.85      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_1580,c_893]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4335,plain,
% 3.17/0.85      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_2998,c_2971]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4362,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,X0) = sK2 | k4_xboole_0(sK2,X0) = k1_xboole_0 ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_2782,c_4335]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1572,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = sK2
% 3.17/0.85      | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = iProver_top ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_888,c_884]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_18,negated_conjecture,
% 3.17/0.85      ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.17/0.85      inference(cnf_transformation,[],[f70]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_886,plain,
% 3.17/0.85      ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1647,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_1572,c_886]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4493,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 | k4_xboole_0(sK2,sK2) = sK2 ),
% 3.17/0.85      inference(superposition,[status(thm)],[c_4362,c_1647]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4518,plain,
% 3.17/0.85      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.17/0.85      inference(demodulation,[status(thm)],[c_4493,c_907]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_17,negated_conjecture,
% 3.17/0.85      ( ~ r1_tarski(sK2,sK3) ),
% 3.17/0.85      inference(cnf_transformation,[],[f62]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_9,plain,
% 3.17/0.85      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.17/0.85      inference(cnf_transformation,[],[f46]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_1013,plain,
% 3.17/0.85      ( r1_tarski(sK2,sK3) | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 3.17/0.85      inference(instantiation,[status(thm)],[c_9]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4687,plain,
% 3.17/0.85      ( sK2 = k1_xboole_0 ),
% 3.17/0.85      inference(global_propositional_subsumption,
% 3.17/0.85                [status(thm)],
% 3.17/0.85                [c_4518,c_17,c_1013]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_887,plain,
% 3.17/0.85      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.17/0.85      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4701,plain,
% 3.17/0.85      ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.17/0.85      inference(demodulation,[status(thm)],[c_4687,c_887]) ).
% 3.17/0.85  
% 3.17/0.85  cnf(c_4769,plain,
% 3.17/0.85      ( $false ),
% 3.17/0.85      inference(forward_subsumption_resolution,[status(thm)],[c_4701,c_1580]) ).
% 3.17/0.85  
% 3.17/0.85  
% 3.17/0.85  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/0.85  
% 3.17/0.85  ------                               Statistics
% 3.17/0.85  
% 3.17/0.85  ------ General
% 3.17/0.85  
% 3.17/0.85  abstr_ref_over_cycles:                  0
% 3.17/0.85  abstr_ref_under_cycles:                 0
% 3.17/0.85  gc_basic_clause_elim:                   0
% 3.17/0.85  forced_gc_time:                         0
% 3.17/0.85  parsing_time:                           0.006
% 3.17/0.85  unif_index_cands_time:                  0.
% 3.17/0.85  unif_index_add_time:                    0.
% 3.17/0.85  orderings_time:                         0.
% 3.17/0.85  out_proof_time:                         0.008
% 3.17/0.85  total_time:                             0.127
% 3.17/0.85  num_of_symbols:                         44
% 3.17/0.85  num_of_terms:                           3701
% 3.17/0.85  
% 3.17/0.85  ------ Preprocessing
% 3.17/0.85  
% 3.17/0.85  num_of_splits:                          0
% 3.17/0.85  num_of_split_atoms:                     0
% 3.17/0.85  num_of_reused_defs:                     0
% 3.17/0.85  num_eq_ax_congr_red:                    12
% 3.17/0.85  num_of_sem_filtered_clauses:            1
% 3.17/0.85  num_of_subtypes:                        0
% 3.17/0.85  monotx_restored_types:                  0
% 3.17/0.85  sat_num_of_epr_types:                   0
% 3.17/0.85  sat_num_of_non_cyclic_types:            0
% 3.17/0.85  sat_guarded_non_collapsed_types:        0
% 3.17/0.85  num_pure_diseq_elim:                    0
% 3.17/0.85  simp_replaced_by:                       0
% 3.17/0.85  res_preprocessed:                       96
% 3.17/0.85  prep_upred:                             0
% 3.17/0.85  prep_unflattend:                        13
% 3.17/0.85  smt_new_axioms:                         0
% 3.17/0.85  pred_elim_cands:                        3
% 3.17/0.85  pred_elim:                              1
% 3.17/0.85  pred_elim_cl:                           1
% 3.17/0.85  pred_elim_cycles:                       3
% 3.17/0.85  merged_defs:                            8
% 3.17/0.85  merged_defs_ncl:                        0
% 3.17/0.85  bin_hyper_res:                          8
% 3.17/0.85  prep_cycles:                            4
% 3.17/0.85  pred_elim_time:                         0.001
% 3.17/0.85  splitting_time:                         0.
% 3.17/0.85  sem_filter_time:                        0.
% 3.17/0.85  monotx_time:                            0.
% 3.17/0.85  subtype_inf_time:                       0.
% 3.17/0.85  
% 3.17/0.85  ------ Problem properties
% 3.17/0.85  
% 3.17/0.85  clauses:                                19
% 3.17/0.85  conjectures:                            3
% 3.17/0.85  epr:                                    7
% 3.17/0.85  horn:                                   16
% 3.17/0.85  ground:                                 3
% 3.17/0.85  unary:                                  9
% 3.17/0.85  binary:                                 7
% 3.17/0.85  lits:                                   32
% 3.17/0.85  lits_eq:                                8
% 3.17/0.85  fd_pure:                                0
% 3.17/0.85  fd_pseudo:                              0
% 3.17/0.85  fd_cond:                                1
% 3.17/0.85  fd_pseudo_cond:                         1
% 3.17/0.85  ac_symbols:                             0
% 3.17/0.85  
% 3.17/0.85  ------ Propositional Solver
% 3.17/0.85  
% 3.17/0.85  prop_solver_calls:                      27
% 3.17/0.85  prop_fast_solver_calls:                 475
% 3.17/0.85  smt_solver_calls:                       0
% 3.17/0.85  smt_fast_solver_calls:                  0
% 3.17/0.85  prop_num_of_clauses:                    1607
% 3.17/0.85  prop_preprocess_simplified:             5319
% 3.17/0.85  prop_fo_subsumed:                       3
% 3.17/0.85  prop_solver_time:                       0.
% 3.17/0.85  smt_solver_time:                        0.
% 3.17/0.85  smt_fast_solver_time:                   0.
% 3.17/0.85  prop_fast_solver_time:                  0.
% 3.17/0.85  prop_unsat_core_time:                   0.
% 3.17/0.85  
% 3.17/0.85  ------ QBF
% 3.17/0.85  
% 3.17/0.85  qbf_q_res:                              0
% 3.17/0.85  qbf_num_tautologies:                    0
% 3.17/0.85  qbf_prep_cycles:                        0
% 3.17/0.85  
% 3.17/0.85  ------ BMC1
% 3.17/0.85  
% 3.17/0.85  bmc1_current_bound:                     -1
% 3.17/0.85  bmc1_last_solved_bound:                 -1
% 3.17/0.85  bmc1_unsat_core_size:                   -1
% 3.17/0.85  bmc1_unsat_core_parents_size:           -1
% 3.17/0.85  bmc1_merge_next_fun:                    0
% 3.17/0.85  bmc1_unsat_core_clauses_time:           0.
% 3.17/0.85  
% 3.17/0.85  ------ Instantiation
% 3.17/0.85  
% 3.17/0.85  inst_num_of_clauses:                    542
% 3.17/0.85  inst_num_in_passive:                    261
% 3.17/0.85  inst_num_in_active:                     232
% 3.17/0.85  inst_num_in_unprocessed:                49
% 3.17/0.85  inst_num_of_loops:                      250
% 3.17/0.85  inst_num_of_learning_restarts:          0
% 3.17/0.85  inst_num_moves_active_passive:          17
% 3.17/0.85  inst_lit_activity:                      0
% 3.17/0.85  inst_lit_activity_moves:                0
% 3.17/0.85  inst_num_tautologies:                   0
% 3.17/0.85  inst_num_prop_implied:                  0
% 3.17/0.85  inst_num_existing_simplified:           0
% 3.17/0.85  inst_num_eq_res_simplified:             0
% 3.17/0.85  inst_num_child_elim:                    0
% 3.17/0.85  inst_num_of_dismatching_blockings:      75
% 3.17/0.85  inst_num_of_non_proper_insts:           406
% 3.17/0.85  inst_num_of_duplicates:                 0
% 3.17/0.85  inst_inst_num_from_inst_to_res:         0
% 3.17/0.85  inst_dismatching_checking_time:         0.
% 3.17/0.85  
% 3.17/0.85  ------ Resolution
% 3.17/0.85  
% 3.17/0.85  res_num_of_clauses:                     0
% 3.17/0.85  res_num_in_passive:                     0
% 3.17/0.85  res_num_in_active:                      0
% 3.17/0.85  res_num_of_loops:                       100
% 3.17/0.85  res_forward_subset_subsumed:            125
% 3.17/0.85  res_backward_subset_subsumed:           0
% 3.17/0.85  res_forward_subsumed:                   0
% 3.17/0.85  res_backward_subsumed:                  0
% 3.17/0.85  res_forward_subsumption_resolution:     1
% 3.17/0.85  res_backward_subsumption_resolution:    0
% 3.17/0.85  res_clause_to_clause_subsumption:       338
% 3.17/0.85  res_orphan_elimination:                 0
% 3.17/0.85  res_tautology_del:                      68
% 3.17/0.85  res_num_eq_res_simplified:              0
% 3.17/0.85  res_num_sel_changes:                    0
% 3.17/0.85  res_moves_from_active_to_pass:          0
% 3.17/0.85  
% 3.17/0.85  ------ Superposition
% 3.17/0.85  
% 3.17/0.85  sup_time_total:                         0.
% 3.17/0.85  sup_time_generating:                    0.
% 3.17/0.85  sup_time_sim_full:                      0.
% 3.17/0.85  sup_time_sim_immed:                     0.
% 3.17/0.85  
% 3.17/0.85  sup_num_of_clauses:                     58
% 3.17/0.85  sup_num_in_active:                      33
% 3.17/0.85  sup_num_in_passive:                     25
% 3.17/0.85  sup_num_of_loops:                       49
% 3.17/0.85  sup_fw_superposition:                   124
% 3.17/0.85  sup_bw_superposition:                   106
% 3.17/0.85  sup_immediate_simplified:               103
% 3.17/0.85  sup_given_eliminated:                   0
% 3.17/0.85  comparisons_done:                       0
% 3.17/0.85  comparisons_avoided:                    3
% 3.17/0.85  
% 3.17/0.85  ------ Simplifications
% 3.17/0.85  
% 3.17/0.85  
% 3.17/0.85  sim_fw_subset_subsumed:                 5
% 3.17/0.85  sim_bw_subset_subsumed:                 2
% 3.17/0.85  sim_fw_subsumed:                        39
% 3.17/0.85  sim_bw_subsumed:                        1
% 3.17/0.85  sim_fw_subsumption_res:                 1
% 3.17/0.85  sim_bw_subsumption_res:                 0
% 3.17/0.85  sim_tautology_del:                      9
% 3.17/0.85  sim_eq_tautology_del:                   28
% 3.17/0.85  sim_eq_res_simp:                        1
% 3.17/0.85  sim_fw_demodulated:                     44
% 3.17/0.85  sim_bw_demodulated:                     14
% 3.17/0.85  sim_light_normalised:                   28
% 3.17/0.85  sim_joinable_taut:                      0
% 3.17/0.85  sim_joinable_simp:                      0
% 3.17/0.85  sim_ac_normalised:                      0
% 3.17/0.85  sim_smt_subsumption:                    0
% 3.17/0.85  
%------------------------------------------------------------------------------
