%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:08 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 187 expanded)
%              Number of clauses        :   40 (  47 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 ( 456 expanded)
%              Number of equality atoms :   52 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f70,plain,(
    ! [X0] :
      ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK2,k3_relat_1(sK3))
        | ~ r2_hidden(sK1,k3_relat_1(sK3)) )
      & r2_hidden(k4_tarski(sK1,sK2),sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r2_hidden(sK2,k3_relat_1(sK3))
      | ~ r2_hidden(sK1,k3_relat_1(sK3)) )
    & r2_hidden(k4_tarski(sK1,sK2),sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f35])).

fof(f59,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(sK3))
    | ~ r2_hidden(sK1,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    r2_hidden(k4_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_291,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_292,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_5,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1261,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1828,plain,
    ( r1_tarski(k4_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3)),k1_zfmisc_1(k3_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_292,c_1261])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1259,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2375,plain,
    ( r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(k3_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1828,c_1259])).

cnf(c_9,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1262,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1966,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1262])).

cnf(c_2857,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_1966])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1464,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2673,plain,
    ( r2_hidden(sK2,k3_relat_1(sK3))
    | ~ r2_hidden(sK2,k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_2674,plain,
    ( r2_hidden(sK2,k3_relat_1(sK3)) = iProver_top
    | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2673])).

cnf(c_1446,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1910,plain,
    ( r2_hidden(sK1,k3_relat_1(sK3))
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_1911,plain,
    ( r2_hidden(sK1,k3_relat_1(sK3)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1910])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1263,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1891,plain,
    ( r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_292,c_1263])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_308,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_309,plain,
    ( r2_hidden(X0,k2_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1358,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),sK3)
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1359,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),sK3) != iProver_top
    | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_296,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_297,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_1355,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),sK3)
    | r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_1356,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),sK3) != iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK1,k3_relat_1(sK3))
    | ~ r2_hidden(sK2,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( r2_hidden(sK1,k3_relat_1(sK3)) != iProver_top
    | r2_hidden(sK2,k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2857,c_2674,c_1911,c_1891,c_1359,c_1356,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n025.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 13:08:50 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 2.11/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/0.93  
% 2.11/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/0.93  
% 2.11/0.93  ------  iProver source info
% 2.11/0.93  
% 2.11/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.11/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/0.93  git: non_committed_changes: false
% 2.11/0.93  git: last_make_outside_of_git: false
% 2.11/0.93  
% 2.11/0.93  ------ 
% 2.11/0.93  
% 2.11/0.93  ------ Input Options
% 2.11/0.93  
% 2.11/0.93  --out_options                           all
% 2.11/0.93  --tptp_safe_out                         true
% 2.11/0.93  --problem_path                          ""
% 2.11/0.93  --include_path                          ""
% 2.11/0.93  --clausifier                            res/vclausify_rel
% 2.11/0.93  --clausifier_options                    --mode clausify
% 2.11/0.93  --stdin                                 false
% 2.11/0.93  --stats_out                             all
% 2.11/0.93  
% 2.11/0.93  ------ General Options
% 2.11/0.93  
% 2.11/0.93  --fof                                   false
% 2.11/0.93  --time_out_real                         305.
% 2.11/0.93  --time_out_virtual                      -1.
% 2.11/0.93  --symbol_type_check                     false
% 2.11/0.93  --clausify_out                          false
% 2.11/0.93  --sig_cnt_out                           false
% 2.11/0.93  --trig_cnt_out                          false
% 2.11/0.93  --trig_cnt_out_tolerance                1.
% 2.11/0.93  --trig_cnt_out_sk_spl                   false
% 2.11/0.93  --abstr_cl_out                          false
% 2.11/0.93  
% 2.11/0.93  ------ Global Options
% 2.11/0.93  
% 2.11/0.93  --schedule                              default
% 2.11/0.93  --add_important_lit                     false
% 2.11/0.93  --prop_solver_per_cl                    1000
% 2.11/0.93  --min_unsat_core                        false
% 2.11/0.93  --soft_assumptions                      false
% 2.11/0.93  --soft_lemma_size                       3
% 2.11/0.93  --prop_impl_unit_size                   0
% 2.11/0.93  --prop_impl_unit                        []
% 2.11/0.93  --share_sel_clauses                     true
% 2.11/0.93  --reset_solvers                         false
% 2.11/0.93  --bc_imp_inh                            [conj_cone]
% 2.11/0.93  --conj_cone_tolerance                   3.
% 2.11/0.93  --extra_neg_conj                        none
% 2.11/0.93  --large_theory_mode                     true
% 2.11/0.93  --prolific_symb_bound                   200
% 2.11/0.93  --lt_threshold                          2000
% 2.11/0.93  --clause_weak_htbl                      true
% 2.11/0.93  --gc_record_bc_elim                     false
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing Options
% 2.11/0.93  
% 2.11/0.93  --preprocessing_flag                    true
% 2.11/0.93  --time_out_prep_mult                    0.1
% 2.11/0.93  --splitting_mode                        input
% 2.11/0.93  --splitting_grd                         true
% 2.11/0.93  --splitting_cvd                         false
% 2.11/0.93  --splitting_cvd_svl                     false
% 2.11/0.93  --splitting_nvd                         32
% 2.11/0.93  --sub_typing                            true
% 2.11/0.93  --prep_gs_sim                           true
% 2.11/0.93  --prep_unflatten                        true
% 2.11/0.93  --prep_res_sim                          true
% 2.11/0.93  --prep_upred                            true
% 2.11/0.93  --prep_sem_filter                       exhaustive
% 2.11/0.93  --prep_sem_filter_out                   false
% 2.11/0.93  --pred_elim                             true
% 2.11/0.93  --res_sim_input                         true
% 2.11/0.93  --eq_ax_congr_red                       true
% 2.11/0.93  --pure_diseq_elim                       true
% 2.11/0.93  --brand_transform                       false
% 2.11/0.93  --non_eq_to_eq                          false
% 2.11/0.93  --prep_def_merge                        true
% 2.11/0.93  --prep_def_merge_prop_impl              false
% 2.11/0.93  --prep_def_merge_mbd                    true
% 2.11/0.93  --prep_def_merge_tr_red                 false
% 2.11/0.93  --prep_def_merge_tr_cl                  false
% 2.11/0.93  --smt_preprocessing                     true
% 2.11/0.93  --smt_ac_axioms                         fast
% 2.11/0.93  --preprocessed_out                      false
% 2.11/0.93  --preprocessed_stats                    false
% 2.11/0.93  
% 2.11/0.93  ------ Abstraction refinement Options
% 2.11/0.93  
% 2.11/0.93  --abstr_ref                             []
% 2.11/0.93  --abstr_ref_prep                        false
% 2.11/0.93  --abstr_ref_until_sat                   false
% 2.11/0.93  --abstr_ref_sig_restrict                funpre
% 2.11/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.93  --abstr_ref_under                       []
% 2.11/0.93  
% 2.11/0.93  ------ SAT Options
% 2.11/0.93  
% 2.11/0.93  --sat_mode                              false
% 2.11/0.93  --sat_fm_restart_options                ""
% 2.11/0.93  --sat_gr_def                            false
% 2.11/0.93  --sat_epr_types                         true
% 2.11/0.93  --sat_non_cyclic_types                  false
% 2.11/0.93  --sat_finite_models                     false
% 2.11/0.93  --sat_fm_lemmas                         false
% 2.11/0.93  --sat_fm_prep                           false
% 2.11/0.93  --sat_fm_uc_incr                        true
% 2.11/0.93  --sat_out_model                         small
% 2.11/0.93  --sat_out_clauses                       false
% 2.11/0.93  
% 2.11/0.93  ------ QBF Options
% 2.11/0.93  
% 2.11/0.93  --qbf_mode                              false
% 2.11/0.93  --qbf_elim_univ                         false
% 2.11/0.93  --qbf_dom_inst                          none
% 2.11/0.93  --qbf_dom_pre_inst                      false
% 2.11/0.93  --qbf_sk_in                             false
% 2.11/0.93  --qbf_pred_elim                         true
% 2.11/0.93  --qbf_split                             512
% 2.11/0.93  
% 2.11/0.93  ------ BMC1 Options
% 2.11/0.93  
% 2.11/0.93  --bmc1_incremental                      false
% 2.11/0.93  --bmc1_axioms                           reachable_all
% 2.11/0.93  --bmc1_min_bound                        0
% 2.11/0.93  --bmc1_max_bound                        -1
% 2.11/0.93  --bmc1_max_bound_default                -1
% 2.11/0.93  --bmc1_symbol_reachability              true
% 2.11/0.93  --bmc1_property_lemmas                  false
% 2.11/0.93  --bmc1_k_induction                      false
% 2.11/0.93  --bmc1_non_equiv_states                 false
% 2.11/0.93  --bmc1_deadlock                         false
% 2.11/0.93  --bmc1_ucm                              false
% 2.11/0.93  --bmc1_add_unsat_core                   none
% 2.11/0.93  --bmc1_unsat_core_children              false
% 2.11/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.93  --bmc1_out_stat                         full
% 2.11/0.93  --bmc1_ground_init                      false
% 2.11/0.93  --bmc1_pre_inst_next_state              false
% 2.11/0.93  --bmc1_pre_inst_state                   false
% 2.11/0.93  --bmc1_pre_inst_reach_state             false
% 2.11/0.93  --bmc1_out_unsat_core                   false
% 2.11/0.93  --bmc1_aig_witness_out                  false
% 2.11/0.93  --bmc1_verbose                          false
% 2.11/0.93  --bmc1_dump_clauses_tptp                false
% 2.11/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.93  --bmc1_dump_file                        -
% 2.11/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.93  --bmc1_ucm_extend_mode                  1
% 2.11/0.93  --bmc1_ucm_init_mode                    2
% 2.11/0.93  --bmc1_ucm_cone_mode                    none
% 2.11/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.93  --bmc1_ucm_relax_model                  4
% 2.11/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.93  --bmc1_ucm_layered_model                none
% 2.11/0.93  --bmc1_ucm_max_lemma_size               10
% 2.11/0.93  
% 2.11/0.93  ------ AIG Options
% 2.11/0.93  
% 2.11/0.93  --aig_mode                              false
% 2.11/0.93  
% 2.11/0.93  ------ Instantiation Options
% 2.11/0.93  
% 2.11/0.93  --instantiation_flag                    true
% 2.11/0.93  --inst_sos_flag                         false
% 2.11/0.93  --inst_sos_phase                        true
% 2.11/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.93  --inst_lit_sel_side                     num_symb
% 2.11/0.93  --inst_solver_per_active                1400
% 2.11/0.93  --inst_solver_calls_frac                1.
% 2.11/0.93  --inst_passive_queue_type               priority_queues
% 2.11/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.93  --inst_passive_queues_freq              [25;2]
% 2.11/0.93  --inst_dismatching                      true
% 2.11/0.93  --inst_eager_unprocessed_to_passive     true
% 2.11/0.93  --inst_prop_sim_given                   true
% 2.11/0.93  --inst_prop_sim_new                     false
% 2.11/0.93  --inst_subs_new                         false
% 2.11/0.93  --inst_eq_res_simp                      false
% 2.11/0.93  --inst_subs_given                       false
% 2.11/0.93  --inst_orphan_elimination               true
% 2.11/0.93  --inst_learning_loop_flag               true
% 2.11/0.93  --inst_learning_start                   3000
% 2.11/0.93  --inst_learning_factor                  2
% 2.11/0.93  --inst_start_prop_sim_after_learn       3
% 2.11/0.93  --inst_sel_renew                        solver
% 2.11/0.93  --inst_lit_activity_flag                true
% 2.11/0.93  --inst_restr_to_given                   false
% 2.11/0.93  --inst_activity_threshold               500
% 2.11/0.93  --inst_out_proof                        true
% 2.11/0.93  
% 2.11/0.93  ------ Resolution Options
% 2.11/0.93  
% 2.11/0.93  --resolution_flag                       true
% 2.11/0.93  --res_lit_sel                           adaptive
% 2.11/0.93  --res_lit_sel_side                      none
% 2.11/0.93  --res_ordering                          kbo
% 2.11/0.93  --res_to_prop_solver                    active
% 2.11/0.93  --res_prop_simpl_new                    false
% 2.11/0.93  --res_prop_simpl_given                  true
% 2.11/0.93  --res_passive_queue_type                priority_queues
% 2.11/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.93  --res_passive_queues_freq               [15;5]
% 2.11/0.93  --res_forward_subs                      full
% 2.11/0.93  --res_backward_subs                     full
% 2.11/0.93  --res_forward_subs_resolution           true
% 2.11/0.93  --res_backward_subs_resolution          true
% 2.11/0.93  --res_orphan_elimination                true
% 2.11/0.93  --res_time_limit                        2.
% 2.11/0.93  --res_out_proof                         true
% 2.11/0.93  
% 2.11/0.93  ------ Superposition Options
% 2.11/0.93  
% 2.11/0.93  --superposition_flag                    true
% 2.11/0.93  --sup_passive_queue_type                priority_queues
% 2.11/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.93  --demod_completeness_check              fast
% 2.11/0.93  --demod_use_ground                      true
% 2.11/0.93  --sup_to_prop_solver                    passive
% 2.11/0.93  --sup_prop_simpl_new                    true
% 2.11/0.93  --sup_prop_simpl_given                  true
% 2.11/0.93  --sup_fun_splitting                     false
% 2.11/0.93  --sup_smt_interval                      50000
% 2.11/0.93  
% 2.11/0.93  ------ Superposition Simplification Setup
% 2.11/0.93  
% 2.11/0.93  --sup_indices_passive                   []
% 2.11/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_full_bw                           [BwDemod]
% 2.11/0.93  --sup_immed_triv                        [TrivRules]
% 2.11/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_immed_bw_main                     []
% 2.11/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.93  
% 2.11/0.93  ------ Combination Options
% 2.11/0.93  
% 2.11/0.93  --comb_res_mult                         3
% 2.11/0.93  --comb_sup_mult                         2
% 2.11/0.93  --comb_inst_mult                        10
% 2.11/0.93  
% 2.11/0.93  ------ Debug Options
% 2.11/0.93  
% 2.11/0.93  --dbg_backtrace                         false
% 2.11/0.93  --dbg_dump_prop_clauses                 false
% 2.11/0.93  --dbg_dump_prop_clauses_file            -
% 2.11/0.93  --dbg_out_stat                          false
% 2.11/0.93  ------ Parsing...
% 2.11/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/0.93  ------ Proving...
% 2.11/0.93  ------ Problem Properties 
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  clauses                                 16
% 2.11/0.93  conjectures                             2
% 2.11/0.93  EPR                                     1
% 2.11/0.93  Horn                                    15
% 2.11/0.93  unary                                   5
% 2.11/0.93  binary                                  9
% 2.11/0.93  lits                                    29
% 2.11/0.93  lits eq                                 2
% 2.11/0.93  fd_pure                                 0
% 2.11/0.93  fd_pseudo                               0
% 2.11/0.93  fd_cond                                 0
% 2.11/0.93  fd_pseudo_cond                          0
% 2.11/0.93  AC symbols                              0
% 2.11/0.93  
% 2.11/0.93  ------ Schedule dynamic 5 is on 
% 2.11/0.93  
% 2.11/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  ------ 
% 2.11/0.93  Current options:
% 2.11/0.93  ------ 
% 2.11/0.93  
% 2.11/0.93  ------ Input Options
% 2.11/0.93  
% 2.11/0.93  --out_options                           all
% 2.11/0.93  --tptp_safe_out                         true
% 2.11/0.93  --problem_path                          ""
% 2.11/0.93  --include_path                          ""
% 2.11/0.93  --clausifier                            res/vclausify_rel
% 2.11/0.93  --clausifier_options                    --mode clausify
% 2.11/0.93  --stdin                                 false
% 2.11/0.93  --stats_out                             all
% 2.11/0.93  
% 2.11/0.93  ------ General Options
% 2.11/0.93  
% 2.11/0.93  --fof                                   false
% 2.11/0.93  --time_out_real                         305.
% 2.11/0.93  --time_out_virtual                      -1.
% 2.11/0.93  --symbol_type_check                     false
% 2.11/0.93  --clausify_out                          false
% 2.11/0.93  --sig_cnt_out                           false
% 2.11/0.93  --trig_cnt_out                          false
% 2.11/0.93  --trig_cnt_out_tolerance                1.
% 2.11/0.93  --trig_cnt_out_sk_spl                   false
% 2.11/0.93  --abstr_cl_out                          false
% 2.11/0.93  
% 2.11/0.93  ------ Global Options
% 2.11/0.93  
% 2.11/0.93  --schedule                              default
% 2.11/0.93  --add_important_lit                     false
% 2.11/0.93  --prop_solver_per_cl                    1000
% 2.11/0.93  --min_unsat_core                        false
% 2.11/0.93  --soft_assumptions                      false
% 2.11/0.93  --soft_lemma_size                       3
% 2.11/0.93  --prop_impl_unit_size                   0
% 2.11/0.93  --prop_impl_unit                        []
% 2.11/0.93  --share_sel_clauses                     true
% 2.11/0.93  --reset_solvers                         false
% 2.11/0.93  --bc_imp_inh                            [conj_cone]
% 2.11/0.93  --conj_cone_tolerance                   3.
% 2.11/0.93  --extra_neg_conj                        none
% 2.11/0.93  --large_theory_mode                     true
% 2.11/0.93  --prolific_symb_bound                   200
% 2.11/0.93  --lt_threshold                          2000
% 2.11/0.93  --clause_weak_htbl                      true
% 2.11/0.93  --gc_record_bc_elim                     false
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing Options
% 2.11/0.93  
% 2.11/0.93  --preprocessing_flag                    true
% 2.11/0.93  --time_out_prep_mult                    0.1
% 2.11/0.93  --splitting_mode                        input
% 2.11/0.93  --splitting_grd                         true
% 2.11/0.93  --splitting_cvd                         false
% 2.11/0.93  --splitting_cvd_svl                     false
% 2.11/0.93  --splitting_nvd                         32
% 2.11/0.93  --sub_typing                            true
% 2.11/0.93  --prep_gs_sim                           true
% 2.11/0.93  --prep_unflatten                        true
% 2.11/0.93  --prep_res_sim                          true
% 2.11/0.93  --prep_upred                            true
% 2.11/0.93  --prep_sem_filter                       exhaustive
% 2.11/0.93  --prep_sem_filter_out                   false
% 2.11/0.93  --pred_elim                             true
% 2.11/0.93  --res_sim_input                         true
% 2.11/0.93  --eq_ax_congr_red                       true
% 2.11/0.93  --pure_diseq_elim                       true
% 2.11/0.93  --brand_transform                       false
% 2.11/0.93  --non_eq_to_eq                          false
% 2.11/0.93  --prep_def_merge                        true
% 2.11/0.93  --prep_def_merge_prop_impl              false
% 2.11/0.93  --prep_def_merge_mbd                    true
% 2.11/0.93  --prep_def_merge_tr_red                 false
% 2.11/0.93  --prep_def_merge_tr_cl                  false
% 2.11/0.93  --smt_preprocessing                     true
% 2.11/0.93  --smt_ac_axioms                         fast
% 2.11/0.93  --preprocessed_out                      false
% 2.11/0.93  --preprocessed_stats                    false
% 2.11/0.93  
% 2.11/0.93  ------ Abstraction refinement Options
% 2.11/0.93  
% 2.11/0.93  --abstr_ref                             []
% 2.11/0.93  --abstr_ref_prep                        false
% 2.11/0.93  --abstr_ref_until_sat                   false
% 2.11/0.93  --abstr_ref_sig_restrict                funpre
% 2.11/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.93  --abstr_ref_under                       []
% 2.11/0.93  
% 2.11/0.93  ------ SAT Options
% 2.11/0.93  
% 2.11/0.93  --sat_mode                              false
% 2.11/0.93  --sat_fm_restart_options                ""
% 2.11/0.93  --sat_gr_def                            false
% 2.11/0.93  --sat_epr_types                         true
% 2.11/0.93  --sat_non_cyclic_types                  false
% 2.11/0.93  --sat_finite_models                     false
% 2.11/0.93  --sat_fm_lemmas                         false
% 2.11/0.93  --sat_fm_prep                           false
% 2.11/0.93  --sat_fm_uc_incr                        true
% 2.11/0.93  --sat_out_model                         small
% 2.11/0.93  --sat_out_clauses                       false
% 2.11/0.93  
% 2.11/0.93  ------ QBF Options
% 2.11/0.93  
% 2.11/0.93  --qbf_mode                              false
% 2.11/0.93  --qbf_elim_univ                         false
% 2.11/0.93  --qbf_dom_inst                          none
% 2.11/0.93  --qbf_dom_pre_inst                      false
% 2.11/0.93  --qbf_sk_in                             false
% 2.11/0.93  --qbf_pred_elim                         true
% 2.11/0.93  --qbf_split                             512
% 2.11/0.93  
% 2.11/0.93  ------ BMC1 Options
% 2.11/0.93  
% 2.11/0.93  --bmc1_incremental                      false
% 2.11/0.93  --bmc1_axioms                           reachable_all
% 2.11/0.93  --bmc1_min_bound                        0
% 2.11/0.93  --bmc1_max_bound                        -1
% 2.11/0.93  --bmc1_max_bound_default                -1
% 2.11/0.93  --bmc1_symbol_reachability              true
% 2.11/0.93  --bmc1_property_lemmas                  false
% 2.11/0.93  --bmc1_k_induction                      false
% 2.11/0.93  --bmc1_non_equiv_states                 false
% 2.11/0.93  --bmc1_deadlock                         false
% 2.11/0.93  --bmc1_ucm                              false
% 2.11/0.93  --bmc1_add_unsat_core                   none
% 2.11/0.93  --bmc1_unsat_core_children              false
% 2.11/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.93  --bmc1_out_stat                         full
% 2.11/0.93  --bmc1_ground_init                      false
% 2.11/0.93  --bmc1_pre_inst_next_state              false
% 2.11/0.93  --bmc1_pre_inst_state                   false
% 2.11/0.93  --bmc1_pre_inst_reach_state             false
% 2.11/0.93  --bmc1_out_unsat_core                   false
% 2.11/0.93  --bmc1_aig_witness_out                  false
% 2.11/0.93  --bmc1_verbose                          false
% 2.11/0.93  --bmc1_dump_clauses_tptp                false
% 2.11/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.93  --bmc1_dump_file                        -
% 2.11/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.93  --bmc1_ucm_extend_mode                  1
% 2.11/0.93  --bmc1_ucm_init_mode                    2
% 2.11/0.93  --bmc1_ucm_cone_mode                    none
% 2.11/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.93  --bmc1_ucm_relax_model                  4
% 2.11/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.93  --bmc1_ucm_layered_model                none
% 2.11/0.93  --bmc1_ucm_max_lemma_size               10
% 2.11/0.93  
% 2.11/0.93  ------ AIG Options
% 2.11/0.93  
% 2.11/0.93  --aig_mode                              false
% 2.11/0.93  
% 2.11/0.93  ------ Instantiation Options
% 2.11/0.93  
% 2.11/0.93  --instantiation_flag                    true
% 2.11/0.93  --inst_sos_flag                         false
% 2.11/0.93  --inst_sos_phase                        true
% 2.11/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.93  --inst_lit_sel_side                     none
% 2.11/0.93  --inst_solver_per_active                1400
% 2.11/0.93  --inst_solver_calls_frac                1.
% 2.11/0.93  --inst_passive_queue_type               priority_queues
% 2.11/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.93  --inst_passive_queues_freq              [25;2]
% 2.11/0.93  --inst_dismatching                      true
% 2.11/0.93  --inst_eager_unprocessed_to_passive     true
% 2.11/0.93  --inst_prop_sim_given                   true
% 2.11/0.93  --inst_prop_sim_new                     false
% 2.11/0.93  --inst_subs_new                         false
% 2.11/0.93  --inst_eq_res_simp                      false
% 2.11/0.93  --inst_subs_given                       false
% 2.11/0.93  --inst_orphan_elimination               true
% 2.11/0.93  --inst_learning_loop_flag               true
% 2.11/0.93  --inst_learning_start                   3000
% 2.11/0.93  --inst_learning_factor                  2
% 2.11/0.93  --inst_start_prop_sim_after_learn       3
% 2.11/0.93  --inst_sel_renew                        solver
% 2.11/0.93  --inst_lit_activity_flag                true
% 2.11/0.93  --inst_restr_to_given                   false
% 2.11/0.93  --inst_activity_threshold               500
% 2.11/0.93  --inst_out_proof                        true
% 2.11/0.93  
% 2.11/0.93  ------ Resolution Options
% 2.11/0.93  
% 2.11/0.93  --resolution_flag                       false
% 2.11/0.93  --res_lit_sel                           adaptive
% 2.11/0.93  --res_lit_sel_side                      none
% 2.11/0.93  --res_ordering                          kbo
% 2.11/0.93  --res_to_prop_solver                    active
% 2.11/0.93  --res_prop_simpl_new                    false
% 2.11/0.93  --res_prop_simpl_given                  true
% 2.11/0.93  --res_passive_queue_type                priority_queues
% 2.11/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.93  --res_passive_queues_freq               [15;5]
% 2.11/0.93  --res_forward_subs                      full
% 2.11/0.93  --res_backward_subs                     full
% 2.11/0.93  --res_forward_subs_resolution           true
% 2.11/0.93  --res_backward_subs_resolution          true
% 2.11/0.93  --res_orphan_elimination                true
% 2.11/0.93  --res_time_limit                        2.
% 2.11/0.93  --res_out_proof                         true
% 2.11/0.93  
% 2.11/0.93  ------ Superposition Options
% 2.11/0.93  
% 2.11/0.93  --superposition_flag                    true
% 2.11/0.93  --sup_passive_queue_type                priority_queues
% 2.11/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.93  --demod_completeness_check              fast
% 2.11/0.93  --demod_use_ground                      true
% 2.11/0.93  --sup_to_prop_solver                    passive
% 2.11/0.93  --sup_prop_simpl_new                    true
% 2.11/0.93  --sup_prop_simpl_given                  true
% 2.11/0.93  --sup_fun_splitting                     false
% 2.11/0.93  --sup_smt_interval                      50000
% 2.11/0.93  
% 2.11/0.93  ------ Superposition Simplification Setup
% 2.11/0.93  
% 2.11/0.93  --sup_indices_passive                   []
% 2.11/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_full_bw                           [BwDemod]
% 2.11/0.93  --sup_immed_triv                        [TrivRules]
% 2.11/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_immed_bw_main                     []
% 2.11/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.93  
% 2.11/0.93  ------ Combination Options
% 2.11/0.93  
% 2.11/0.93  --comb_res_mult                         3
% 2.11/0.93  --comb_sup_mult                         2
% 2.11/0.93  --comb_inst_mult                        10
% 2.11/0.93  
% 2.11/0.93  ------ Debug Options
% 2.11/0.93  
% 2.11/0.93  --dbg_backtrace                         false
% 2.11/0.93  --dbg_dump_prop_clauses                 false
% 2.11/0.93  --dbg_dump_prop_clauses_file            -
% 2.11/0.93  --dbg_out_stat                          false
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  ------ Proving...
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  % SZS status Theorem for theBenchmark.p
% 2.11/0.93  
% 2.11/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/0.93  
% 2.11/0.93  fof(f15,axiom,(
% 2.11/0.93    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f23,plain,(
% 2.11/0.93    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 2.11/0.93    inference(ennf_transformation,[],[f15])).
% 2.11/0.93  
% 2.11/0.93  fof(f56,plain,(
% 2.11/0.93    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f23])).
% 2.11/0.93  
% 2.11/0.93  fof(f8,axiom,(
% 2.11/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f46,plain,(
% 2.11/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.11/0.93    inference(cnf_transformation,[],[f8])).
% 2.11/0.93  
% 2.11/0.93  fof(f3,axiom,(
% 2.11/0.93    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f41,plain,(
% 2.11/0.93    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f3])).
% 2.11/0.93  
% 2.11/0.93  fof(f4,axiom,(
% 2.11/0.93    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f42,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f4])).
% 2.11/0.93  
% 2.11/0.93  fof(f5,axiom,(
% 2.11/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f43,plain,(
% 2.11/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f5])).
% 2.11/0.93  
% 2.11/0.93  fof(f6,axiom,(
% 2.11/0.93    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f44,plain,(
% 2.11/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f6])).
% 2.11/0.93  
% 2.11/0.93  fof(f62,plain,(
% 2.11/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.11/0.93    inference(definition_unfolding,[],[f43,f44])).
% 2.11/0.93  
% 2.11/0.93  fof(f63,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.11/0.93    inference(definition_unfolding,[],[f42,f62])).
% 2.11/0.93  
% 2.11/0.93  fof(f64,plain,(
% 2.11/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.11/0.93    inference(definition_unfolding,[],[f41,f63])).
% 2.11/0.93  
% 2.11/0.93  fof(f65,plain,(
% 2.11/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.11/0.93    inference(definition_unfolding,[],[f46,f64])).
% 2.11/0.93  
% 2.11/0.93  fof(f70,plain,(
% 2.11/0.93    ( ! [X0] : (k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.11/0.93    inference(definition_unfolding,[],[f56,f65])).
% 2.11/0.93  
% 2.11/0.93  fof(f17,conjecture,(
% 2.11/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f18,negated_conjecture,(
% 2.11/0.93    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.11/0.93    inference(negated_conjecture,[],[f17])).
% 2.11/0.93  
% 2.11/0.93  fof(f26,plain,(
% 2.11/0.93    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 2.11/0.93    inference(ennf_transformation,[],[f18])).
% 2.11/0.93  
% 2.11/0.93  fof(f27,plain,(
% 2.11/0.93    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 2.11/0.93    inference(flattening,[],[f26])).
% 2.11/0.93  
% 2.11/0.93  fof(f35,plain,(
% 2.11/0.93    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK2,k3_relat_1(sK3)) | ~r2_hidden(sK1,k3_relat_1(sK3))) & r2_hidden(k4_tarski(sK1,sK2),sK3) & v1_relat_1(sK3))),
% 2.11/0.93    introduced(choice_axiom,[])).
% 2.11/0.93  
% 2.11/0.93  fof(f36,plain,(
% 2.11/0.93    (~r2_hidden(sK2,k3_relat_1(sK3)) | ~r2_hidden(sK1,k3_relat_1(sK3))) & r2_hidden(k4_tarski(sK1,sK2),sK3) & v1_relat_1(sK3)),
% 2.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f35])).
% 2.11/0.93  
% 2.11/0.93  fof(f59,plain,(
% 2.11/0.93    v1_relat_1(sK3)),
% 2.11/0.93    inference(cnf_transformation,[],[f36])).
% 2.11/0.93  
% 2.11/0.93  fof(f9,axiom,(
% 2.11/0.93    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f47,plain,(
% 2.11/0.93    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 2.11/0.93    inference(cnf_transformation,[],[f9])).
% 2.11/0.93  
% 2.11/0.93  fof(f10,axiom,(
% 2.11/0.93    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f32,plain,(
% 2.11/0.93    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.11/0.93    inference(nnf_transformation,[],[f10])).
% 2.11/0.93  
% 2.11/0.93  fof(f33,plain,(
% 2.11/0.93    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.11/0.93    inference(flattening,[],[f32])).
% 2.11/0.93  
% 2.11/0.93  fof(f49,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f33])).
% 2.11/0.93  
% 2.11/0.93  fof(f68,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 2.11/0.93    inference(definition_unfolding,[],[f49,f64])).
% 2.11/0.93  
% 2.11/0.93  fof(f11,axiom,(
% 2.11/0.93    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f51,plain,(
% 2.11/0.93    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.11/0.93    inference(cnf_transformation,[],[f11])).
% 2.11/0.93  
% 2.11/0.93  fof(f7,axiom,(
% 2.11/0.93    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f20,plain,(
% 2.11/0.93    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.11/0.93    inference(ennf_transformation,[],[f7])).
% 2.11/0.93  
% 2.11/0.93  fof(f45,plain,(
% 2.11/0.93    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f20])).
% 2.11/0.93  
% 2.11/0.93  fof(f1,axiom,(
% 2.11/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f19,plain,(
% 2.11/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.93    inference(ennf_transformation,[],[f1])).
% 2.11/0.93  
% 2.11/0.93  fof(f28,plain,(
% 2.11/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.93    inference(nnf_transformation,[],[f19])).
% 2.11/0.93  
% 2.11/0.93  fof(f29,plain,(
% 2.11/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.93    inference(rectify,[],[f28])).
% 2.11/0.93  
% 2.11/0.93  fof(f30,plain,(
% 2.11/0.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.11/0.93    introduced(choice_axiom,[])).
% 2.11/0.93  
% 2.11/0.93  fof(f31,plain,(
% 2.11/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.11/0.93  
% 2.11/0.93  fof(f37,plain,(
% 2.11/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f31])).
% 2.11/0.93  
% 2.11/0.93  fof(f2,axiom,(
% 2.11/0.93    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f40,plain,(
% 2.11/0.93    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.93    inference(cnf_transformation,[],[f2])).
% 2.11/0.93  
% 2.11/0.93  fof(f66,plain,(
% 2.11/0.93    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 2.11/0.93    inference(definition_unfolding,[],[f40,f65])).
% 2.11/0.93  
% 2.11/0.93  fof(f16,axiom,(
% 2.11/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.11/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.93  
% 2.11/0.93  fof(f24,plain,(
% 2.11/0.93    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.11/0.93    inference(ennf_transformation,[],[f16])).
% 2.11/0.93  
% 2.11/0.93  fof(f25,plain,(
% 2.11/0.93    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.11/0.93    inference(flattening,[],[f24])).
% 2.11/0.93  
% 2.11/0.93  fof(f58,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f25])).
% 2.11/0.93  
% 2.11/0.93  fof(f57,plain,(
% 2.11/0.93    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.11/0.93    inference(cnf_transformation,[],[f25])).
% 2.11/0.93  
% 2.11/0.93  fof(f61,plain,(
% 2.11/0.93    ~r2_hidden(sK2,k3_relat_1(sK3)) | ~r2_hidden(sK1,k3_relat_1(sK3))),
% 2.11/0.93    inference(cnf_transformation,[],[f36])).
% 2.11/0.93  
% 2.11/0.93  fof(f60,plain,(
% 2.11/0.93    r2_hidden(k4_tarski(sK1,sK2),sK3)),
% 2.11/0.93    inference(cnf_transformation,[],[f36])).
% 2.11/0.93  
% 2.11/0.93  cnf(c_14,plain,
% 2.11/0.93      ( ~ v1_relat_1(X0)
% 2.11/0.93      | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 2.11/0.93      inference(cnf_transformation,[],[f70]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_19,negated_conjecture,
% 2.11/0.93      ( v1_relat_1(sK3) ),
% 2.11/0.93      inference(cnf_transformation,[],[f59]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_291,plain,
% 2.11/0.93      ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 2.11/0.93      | sK3 != X0 ),
% 2.11/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_292,plain,
% 2.11/0.93      ( k3_tarski(k4_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
% 2.11/0.93      inference(unflattening,[status(thm)],[c_291]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_5,plain,
% 2.11/0.93      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 2.11/0.93      inference(cnf_transformation,[],[f47]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1261,plain,
% 2.11/0.93      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1828,plain,
% 2.11/0.93      ( r1_tarski(k4_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3)),k1_zfmisc_1(k3_relat_1(sK3))) = iProver_top ),
% 2.11/0.93      inference(superposition,[status(thm)],[c_292,c_1261]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_7,plain,
% 2.11/0.93      ( r2_hidden(X0,X1)
% 2.11/0.93      | ~ r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
% 2.11/0.93      inference(cnf_transformation,[],[f68]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1259,plain,
% 2.11/0.93      ( r2_hidden(X0,X1) = iProver_top
% 2.11/0.93      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_2375,plain,
% 2.11/0.93      ( r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(k3_relat_1(sK3))) = iProver_top ),
% 2.11/0.93      inference(superposition,[status(thm)],[c_1828,c_1259]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_9,plain,
% 2.11/0.93      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.11/0.93      inference(cnf_transformation,[],[f51]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_4,plain,
% 2.11/0.93      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 2.11/0.93      inference(cnf_transformation,[],[f45]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1262,plain,
% 2.11/0.93      ( r2_hidden(X0,X1) != iProver_top
% 2.11/0.93      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1966,plain,
% 2.11/0.93      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.11/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.11/0.93      inference(superposition,[status(thm)],[c_9,c_1262]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_2857,plain,
% 2.11/0.93      ( r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
% 2.11/0.93      inference(superposition,[status(thm)],[c_2375,c_1966]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_2,plain,
% 2.11/0.93      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.11/0.93      inference(cnf_transformation,[],[f37]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1464,plain,
% 2.11/0.93      ( r2_hidden(sK2,X0)
% 2.11/0.93      | ~ r2_hidden(sK2,k2_relat_1(sK3))
% 2.11/0.93      | ~ r1_tarski(k2_relat_1(sK3),X0) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_2673,plain,
% 2.11/0.93      ( r2_hidden(sK2,k3_relat_1(sK3))
% 2.11/0.93      | ~ r2_hidden(sK2,k2_relat_1(sK3))
% 2.11/0.93      | ~ r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_1464]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_2674,plain,
% 2.11/0.93      ( r2_hidden(sK2,k3_relat_1(sK3)) = iProver_top
% 2.11/0.93      | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top
% 2.11/0.93      | r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) != iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_2673]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1446,plain,
% 2.11/0.93      ( r2_hidden(sK1,X0)
% 2.11/0.93      | ~ r2_hidden(sK1,k1_relat_1(sK3))
% 2.11/0.93      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1910,plain,
% 2.11/0.93      ( r2_hidden(sK1,k3_relat_1(sK3))
% 2.11/0.93      | ~ r2_hidden(sK1,k1_relat_1(sK3))
% 2.11/0.93      | ~ r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_1446]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1911,plain,
% 2.11/0.93      ( r2_hidden(sK1,k3_relat_1(sK3)) = iProver_top
% 2.11/0.93      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 2.11/0.93      | r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) != iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_1910]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_3,plain,
% 2.11/0.93      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 2.11/0.93      inference(cnf_transformation,[],[f66]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1263,plain,
% 2.11/0.93      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1891,plain,
% 2.11/0.93      ( r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
% 2.11/0.93      inference(superposition,[status(thm)],[c_292,c_1263]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_15,plain,
% 2.11/0.93      ( r2_hidden(X0,k2_relat_1(X1))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.11/0.93      | ~ v1_relat_1(X1) ),
% 2.11/0.93      inference(cnf_transformation,[],[f58]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_308,plain,
% 2.11/0.93      ( r2_hidden(X0,k2_relat_1(X1))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.11/0.93      | sK3 != X1 ),
% 2.11/0.93      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_309,plain,
% 2.11/0.93      ( r2_hidden(X0,k2_relat_1(sK3))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.11/0.93      inference(unflattening,[status(thm)],[c_308]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1358,plain,
% 2.11/0.93      ( ~ r2_hidden(k4_tarski(sK1,sK2),sK3)
% 2.11/0.93      | r2_hidden(sK2,k2_relat_1(sK3)) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_309]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1359,plain,
% 2.11/0.93      ( r2_hidden(k4_tarski(sK1,sK2),sK3) != iProver_top
% 2.11/0.93      | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_16,plain,
% 2.11/0.93      ( r2_hidden(X0,k1_relat_1(X1))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.11/0.93      | ~ v1_relat_1(X1) ),
% 2.11/0.93      inference(cnf_transformation,[],[f57]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_296,plain,
% 2.11/0.93      ( r2_hidden(X0,k1_relat_1(X1))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.11/0.93      | sK3 != X1 ),
% 2.11/0.93      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_297,plain,
% 2.11/0.93      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.11/0.93      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
% 2.11/0.93      inference(unflattening,[status(thm)],[c_296]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1355,plain,
% 2.11/0.93      ( ~ r2_hidden(k4_tarski(sK1,sK2),sK3)
% 2.11/0.93      | r2_hidden(sK1,k1_relat_1(sK3)) ),
% 2.11/0.93      inference(instantiation,[status(thm)],[c_297]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_1356,plain,
% 2.11/0.93      ( r2_hidden(k4_tarski(sK1,sK2),sK3) != iProver_top
% 2.11/0.93      | r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_1355]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_17,negated_conjecture,
% 2.11/0.93      ( ~ r2_hidden(sK1,k3_relat_1(sK3))
% 2.11/0.93      | ~ r2_hidden(sK2,k3_relat_1(sK3)) ),
% 2.11/0.93      inference(cnf_transformation,[],[f61]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_22,plain,
% 2.11/0.93      ( r2_hidden(sK1,k3_relat_1(sK3)) != iProver_top
% 2.11/0.93      | r2_hidden(sK2,k3_relat_1(sK3)) != iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_18,negated_conjecture,
% 2.11/0.93      ( r2_hidden(k4_tarski(sK1,sK2),sK3) ),
% 2.11/0.93      inference(cnf_transformation,[],[f60]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(c_21,plain,
% 2.11/0.93      ( r2_hidden(k4_tarski(sK1,sK2),sK3) = iProver_top ),
% 2.11/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.11/0.93  
% 2.11/0.93  cnf(contradiction,plain,
% 2.11/0.93      ( $false ),
% 2.11/0.93      inference(minisat,
% 2.11/0.93                [status(thm)],
% 2.11/0.93                [c_2857,c_2674,c_1911,c_1891,c_1359,c_1356,c_22,c_21]) ).
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/0.93  
% 2.11/0.93  ------                               Statistics
% 2.11/0.93  
% 2.11/0.93  ------ General
% 2.11/0.93  
% 2.11/0.93  abstr_ref_over_cycles:                  0
% 2.11/0.93  abstr_ref_under_cycles:                 0
% 2.11/0.93  gc_basic_clause_elim:                   0
% 2.11/0.93  forced_gc_time:                         0
% 2.11/0.93  parsing_time:                           0.009
% 2.11/0.93  unif_index_cands_time:                  0.
% 2.11/0.93  unif_index_add_time:                    0.
% 2.11/0.93  orderings_time:                         0.
% 2.11/0.93  out_proof_time:                         0.011
% 2.11/0.93  total_time:                             0.107
% 2.11/0.93  num_of_symbols:                         47
% 2.11/0.93  num_of_terms:                           2637
% 2.11/0.93  
% 2.11/0.93  ------ Preprocessing
% 2.11/0.93  
% 2.11/0.93  num_of_splits:                          0
% 2.11/0.93  num_of_split_atoms:                     0
% 2.11/0.93  num_of_reused_defs:                     0
% 2.11/0.93  num_eq_ax_congr_red:                    9
% 2.11/0.93  num_of_sem_filtered_clauses:            1
% 2.11/0.93  num_of_subtypes:                        0
% 2.11/0.93  monotx_restored_types:                  0
% 2.11/0.93  sat_num_of_epr_types:                   0
% 2.11/0.93  sat_num_of_non_cyclic_types:            0
% 2.11/0.93  sat_guarded_non_collapsed_types:        0
% 2.11/0.93  num_pure_diseq_elim:                    0
% 2.11/0.93  simp_replaced_by:                       0
% 2.11/0.93  res_preprocessed:                       91
% 2.11/0.93  prep_upred:                             0
% 2.11/0.93  prep_unflattend:                        86
% 2.11/0.93  smt_new_axioms:                         0
% 2.11/0.93  pred_elim_cands:                        2
% 2.11/0.93  pred_elim:                              3
% 2.11/0.93  pred_elim_cl:                           4
% 2.11/0.93  pred_elim_cycles:                       5
% 2.11/0.93  merged_defs:                            2
% 2.11/0.93  merged_defs_ncl:                        0
% 2.11/0.93  bin_hyper_res:                          2
% 2.11/0.93  prep_cycles:                            4
% 2.11/0.93  pred_elim_time:                         0.008
% 2.11/0.93  splitting_time:                         0.
% 2.11/0.93  sem_filter_time:                        0.
% 2.11/0.93  monotx_time:                            0.
% 2.11/0.93  subtype_inf_time:                       0.
% 2.11/0.93  
% 2.11/0.93  ------ Problem properties
% 2.11/0.93  
% 2.11/0.93  clauses:                                16
% 2.11/0.93  conjectures:                            2
% 2.11/0.93  epr:                                    1
% 2.11/0.93  horn:                                   15
% 2.11/0.93  ground:                                 3
% 2.11/0.93  unary:                                  5
% 2.11/0.93  binary:                                 9
% 2.11/0.93  lits:                                   29
% 2.11/0.93  lits_eq:                                2
% 2.11/0.93  fd_pure:                                0
% 2.11/0.93  fd_pseudo:                              0
% 2.11/0.93  fd_cond:                                0
% 2.11/0.93  fd_pseudo_cond:                         0
% 2.11/0.93  ac_symbols:                             0
% 2.11/0.93  
% 2.11/0.93  ------ Propositional Solver
% 2.11/0.93  
% 2.11/0.93  prop_solver_calls:                      25
% 2.11/0.93  prop_fast_solver_calls:                 526
% 2.11/0.93  smt_solver_calls:                       0
% 2.11/0.93  smt_fast_solver_calls:                  0
% 2.11/0.93  prop_num_of_clauses:                    996
% 2.11/0.93  prop_preprocess_simplified:             4248
% 2.11/0.93  prop_fo_subsumed:                       0
% 2.11/0.93  prop_solver_time:                       0.
% 2.11/0.93  smt_solver_time:                        0.
% 2.11/0.93  smt_fast_solver_time:                   0.
% 2.11/0.93  prop_fast_solver_time:                  0.
% 2.11/0.93  prop_unsat_core_time:                   0.
% 2.11/0.93  
% 2.11/0.93  ------ QBF
% 2.11/0.93  
% 2.11/0.93  qbf_q_res:                              0
% 2.11/0.93  qbf_num_tautologies:                    0
% 2.11/0.93  qbf_prep_cycles:                        0
% 2.11/0.93  
% 2.11/0.93  ------ BMC1
% 2.11/0.93  
% 2.11/0.93  bmc1_current_bound:                     -1
% 2.11/0.93  bmc1_last_solved_bound:                 -1
% 2.11/0.93  bmc1_unsat_core_size:                   -1
% 2.11/0.93  bmc1_unsat_core_parents_size:           -1
% 2.11/0.93  bmc1_merge_next_fun:                    0
% 2.11/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.11/0.93  
% 2.11/0.93  ------ Instantiation
% 2.11/0.93  
% 2.11/0.93  inst_num_of_clauses:                    274
% 2.11/0.93  inst_num_in_passive:                    113
% 2.11/0.93  inst_num_in_active:                     127
% 2.11/0.93  inst_num_in_unprocessed:                34
% 2.11/0.93  inst_num_of_loops:                      140
% 2.11/0.93  inst_num_of_learning_restarts:          0
% 2.11/0.93  inst_num_moves_active_passive:          12
% 2.11/0.93  inst_lit_activity:                      0
% 2.11/0.93  inst_lit_activity_moves:                0
% 2.11/0.93  inst_num_tautologies:                   0
% 2.11/0.93  inst_num_prop_implied:                  0
% 2.11/0.93  inst_num_existing_simplified:           0
% 2.11/0.93  inst_num_eq_res_simplified:             0
% 2.11/0.93  inst_num_child_elim:                    0
% 2.11/0.93  inst_num_of_dismatching_blockings:      26
% 2.11/0.93  inst_num_of_non_proper_insts:           155
% 2.11/0.93  inst_num_of_duplicates:                 0
% 2.11/0.93  inst_inst_num_from_inst_to_res:         0
% 2.11/0.93  inst_dismatching_checking_time:         0.
% 2.11/0.93  
% 2.11/0.93  ------ Resolution
% 2.11/0.93  
% 2.11/0.93  res_num_of_clauses:                     0
% 2.11/0.93  res_num_in_passive:                     0
% 2.11/0.93  res_num_in_active:                      0
% 2.11/0.93  res_num_of_loops:                       95
% 2.11/0.93  res_forward_subset_subsumed:            17
% 2.11/0.93  res_backward_subset_subsumed:           0
% 2.11/0.93  res_forward_subsumed:                   0
% 2.11/0.93  res_backward_subsumed:                  0
% 2.11/0.93  res_forward_subsumption_resolution:     0
% 2.11/0.93  res_backward_subsumption_resolution:    0
% 2.11/0.93  res_clause_to_clause_subsumption:       100
% 2.11/0.93  res_orphan_elimination:                 0
% 2.11/0.93  res_tautology_del:                      19
% 2.11/0.93  res_num_eq_res_simplified:              0
% 2.11/0.93  res_num_sel_changes:                    0
% 2.11/0.93  res_moves_from_active_to_pass:          0
% 2.11/0.93  
% 2.11/0.93  ------ Superposition
% 2.11/0.93  
% 2.11/0.93  sup_time_total:                         0.
% 2.11/0.93  sup_time_generating:                    0.
% 2.11/0.93  sup_time_sim_full:                      0.
% 2.11/0.93  sup_time_sim_immed:                     0.
% 2.11/0.93  
% 2.11/0.93  sup_num_of_clauses:                     50
% 2.11/0.93  sup_num_in_active:                      28
% 2.11/0.93  sup_num_in_passive:                     22
% 2.11/0.93  sup_num_of_loops:                       27
% 2.11/0.93  sup_fw_superposition:                   23
% 2.11/0.93  sup_bw_superposition:                   16
% 2.11/0.93  sup_immediate_simplified:               2
% 2.11/0.93  sup_given_eliminated:                   0
% 2.11/0.93  comparisons_done:                       0
% 2.11/0.93  comparisons_avoided:                    0
% 2.11/0.93  
% 2.11/0.93  ------ Simplifications
% 2.11/0.93  
% 2.11/0.93  
% 2.11/0.93  sim_fw_subset_subsumed:                 2
% 2.11/0.93  sim_bw_subset_subsumed:                 0
% 2.11/0.93  sim_fw_subsumed:                        0
% 2.11/0.93  sim_bw_subsumed:                        0
% 2.11/0.93  sim_fw_subsumption_res:                 0
% 2.11/0.93  sim_bw_subsumption_res:                 0
% 2.11/0.93  sim_tautology_del:                      3
% 2.11/0.93  sim_eq_tautology_del:                   0
% 2.11/0.93  sim_eq_res_simp:                        0
% 2.11/0.93  sim_fw_demodulated:                     0
% 2.11/0.93  sim_bw_demodulated:                     0
% 2.11/0.93  sim_light_normalised:                   0
% 2.11/0.93  sim_joinable_taut:                      0
% 2.11/0.93  sim_joinable_simp:                      0
% 2.11/0.93  sim_ac_normalised:                      0
% 2.11/0.93  sim_smt_subsumption:                    0
% 2.11/0.93  
%------------------------------------------------------------------------------
