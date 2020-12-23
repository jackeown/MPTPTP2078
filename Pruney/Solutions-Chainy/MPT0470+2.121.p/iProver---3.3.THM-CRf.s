%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:16 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 377 expanded)
%              Number of clauses        :   68 ( 117 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 ( 744 expanded)
%              Number of equality atoms :  161 ( 420 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f40])).

fof(f64,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f72,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_454,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_460,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_465,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_462,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1211,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_462])).

cnf(c_1940,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_1211])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_458,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_457,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1204,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_457])).

cnf(c_2975,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1940,c_1204])).

cnf(c_11954,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_454,c_2975])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_456,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_860,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_456])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_874,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_860,c_16])).

cnf(c_35,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_37,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1016,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | ~ r1_xboole_0(k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),X1),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1408,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1410,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_1409,plain,
    ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1412,plain,
    ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1579,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_874,c_37,c_1410,c_1412])).

cnf(c_1580,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1579])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_466,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1586,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1580,c_466])).

cnf(c_1591,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_1586])).

cnf(c_11961,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_11954,c_1591])).

cnf(c_2,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_468,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_463,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_467,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_974,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_463,c_467])).

cnf(c_1743,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_468,c_974])).

cnf(c_11962,plain,
    ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11961,c_2,c_1743])).

cnf(c_2974,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_1204])).

cnf(c_11326,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1940,c_2974])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_455,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_635,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_455])).

cnf(c_649,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_635,c_15])).

cnf(c_1349,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_649,c_466])).

cnf(c_1354,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_1349])).

cnf(c_36,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1370,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1354])).

cnf(c_2223,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1354,c_36,c_1370,c_1408,c_1409])).

cnf(c_11328,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_11326,c_2223])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_464,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1046,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_464,c_467])).

cnf(c_2128,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_468,c_1046])).

cnf(c_11329,plain,
    ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11328,c_2,c_2128])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11347,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11329,c_17])).

cnf(c_11348,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11347])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11962,c_11348])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.64/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.49  
% 7.64/1.49  ------  iProver source info
% 7.64/1.49  
% 7.64/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.49  git: non_committed_changes: false
% 7.64/1.49  git: last_make_outside_of_git: false
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    --mode clausify
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             sel
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         604.99
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              none
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           false
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             false
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         false
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     num_symb
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       true
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     false
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   []
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_full_bw                           [BwDemod]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  ------ Parsing...
% 7.64/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.49  ------ Proving...
% 7.64/1.49  ------ Problem Properties 
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  clauses                                 19
% 7.64/1.49  conjectures                             2
% 7.64/1.49  EPR                                     5
% 7.64/1.49  Horn                                    18
% 7.64/1.49  unary                                   7
% 7.64/1.49  binary                                  8
% 7.64/1.49  lits                                    37
% 7.64/1.49  lits eq                                 11
% 7.64/1.49  fd_pure                                 0
% 7.64/1.49  fd_pseudo                               0
% 7.64/1.49  fd_cond                                 1
% 7.64/1.49  fd_pseudo_cond                          0
% 7.64/1.49  AC symbols                              0
% 7.64/1.49  
% 7.64/1.49  ------ Input Options Time Limit: Unbounded
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  Current options:
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    --mode clausify
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             sel
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         604.99
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              none
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           false
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             false
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         false
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     num_symb
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       true
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     false
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   []
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_full_bw                           [BwDemod]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ Proving...
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS status Theorem for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  fof(f20,conjecture,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f21,negated_conjecture,(
% 7.64/1.49    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.64/1.49    inference(negated_conjecture,[],[f20])).
% 7.64/1.49  
% 7.64/1.49  fof(f34,plain,(
% 7.64/1.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f21])).
% 7.64/1.49  
% 7.64/1.49  fof(f40,plain,(
% 7.64/1.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f41,plain,(
% 7.64/1.49    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f40])).
% 7.64/1.49  
% 7.64/1.49  fof(f64,plain,(
% 7.64/1.49    v1_relat_1(sK3)),
% 7.64/1.49    inference(cnf_transformation,[],[f41])).
% 7.64/1.49  
% 7.64/1.49  fof(f14,axiom,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f26,plain,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f14])).
% 7.64/1.49  
% 7.64/1.49  fof(f35,plain,(
% 7.64/1.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 7.64/1.49    inference(nnf_transformation,[],[f26])).
% 7.64/1.49  
% 7.64/1.49  fof(f36,plain,(
% 7.64/1.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.64/1.49    inference(rectify,[],[f35])).
% 7.64/1.49  
% 7.64/1.49  fof(f38,plain,(
% 7.64/1.49    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f37,plain,(
% 7.64/1.49    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f39,plain,(
% 7.64/1.49    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).
% 7.64/1.49  
% 7.64/1.49  fof(f56,plain,(
% 7.64/1.49    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f39])).
% 7.64/1.49  
% 7.64/1.49  fof(f5,axiom,(
% 7.64/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f46,plain,(
% 7.64/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f5])).
% 7.64/1.49  
% 7.64/1.49  fof(f12,axiom,(
% 7.64/1.49    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f25,plain,(
% 7.64/1.49    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 7.64/1.49    inference(ennf_transformation,[],[f12])).
% 7.64/1.49  
% 7.64/1.49  fof(f53,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f25])).
% 7.64/1.49  
% 7.64/1.49  fof(f6,axiom,(
% 7.64/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f47,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f6])).
% 7.64/1.49  
% 7.64/1.49  fof(f7,axiom,(
% 7.64/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f48,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f7])).
% 7.64/1.49  
% 7.64/1.49  fof(f8,axiom,(
% 7.64/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f49,plain,(
% 7.64/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f8])).
% 7.64/1.49  
% 7.64/1.49  fof(f9,axiom,(
% 7.64/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f50,plain,(
% 7.64/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f9])).
% 7.64/1.49  
% 7.64/1.49  fof(f66,plain,(
% 7.64/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f49,f50])).
% 7.64/1.49  
% 7.64/1.49  fof(f67,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f48,f66])).
% 7.64/1.49  
% 7.64/1.49  fof(f68,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f47,f67])).
% 7.64/1.49  
% 7.64/1.49  fof(f71,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f53,f68])).
% 7.64/1.49  
% 7.64/1.49  fof(f15,axiom,(
% 7.64/1.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f27,plain,(
% 7.64/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f15])).
% 7.64/1.49  
% 7.64/1.49  fof(f28,plain,(
% 7.64/1.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(flattening,[],[f27])).
% 7.64/1.49  
% 7.64/1.49  fof(f58,plain,(
% 7.64/1.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f28])).
% 7.64/1.49  
% 7.64/1.49  fof(f16,axiom,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f29,plain,(
% 7.64/1.49    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f16])).
% 7.64/1.49  
% 7.64/1.49  fof(f59,plain,(
% 7.64/1.49    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f29])).
% 7.64/1.49  
% 7.64/1.49  fof(f13,axiom,(
% 7.64/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f54,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f13])).
% 7.64/1.49  
% 7.64/1.49  fof(f69,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.64/1.49    inference(definition_unfolding,[],[f54,f68])).
% 7.64/1.49  
% 7.64/1.49  fof(f72,plain,(
% 7.64/1.49    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f59,f69])).
% 7.64/1.49  
% 7.64/1.49  fof(f19,axiom,(
% 7.64/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f63,plain,(
% 7.64/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.64/1.49    inference(cnf_transformation,[],[f19])).
% 7.64/1.49  
% 7.64/1.49  fof(f17,axiom,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f30,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f17])).
% 7.64/1.49  
% 7.64/1.49  fof(f31,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(flattening,[],[f30])).
% 7.64/1.49  
% 7.64/1.49  fof(f60,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f31])).
% 7.64/1.49  
% 7.64/1.49  fof(f62,plain,(
% 7.64/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.64/1.49    inference(cnf_transformation,[],[f19])).
% 7.64/1.49  
% 7.64/1.49  fof(f4,axiom,(
% 7.64/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f45,plain,(
% 7.64/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f4])).
% 7.64/1.49  
% 7.64/1.49  fof(f3,axiom,(
% 7.64/1.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f44,plain,(
% 7.64/1.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f3])).
% 7.64/1.49  
% 7.64/1.49  fof(f70,plain,(
% 7.64/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 7.64/1.49    inference(definition_unfolding,[],[f44,f69])).
% 7.64/1.49  
% 7.64/1.49  fof(f1,axiom,(
% 7.64/1.49    v1_xboole_0(k1_xboole_0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f42,plain,(
% 7.64/1.49    v1_xboole_0(k1_xboole_0)),
% 7.64/1.49    inference(cnf_transformation,[],[f1])).
% 7.64/1.49  
% 7.64/1.49  fof(f11,axiom,(
% 7.64/1.49    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f24,plain,(
% 7.64/1.49    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f11])).
% 7.64/1.49  
% 7.64/1.49  fof(f52,plain,(
% 7.64/1.49    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f24])).
% 7.64/1.49  
% 7.64/1.49  fof(f2,axiom,(
% 7.64/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f22,plain,(
% 7.64/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f2])).
% 7.64/1.49  
% 7.64/1.49  fof(f43,plain,(
% 7.64/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f22])).
% 7.64/1.49  
% 7.64/1.49  fof(f18,axiom,(
% 7.64/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f32,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f18])).
% 7.64/1.49  
% 7.64/1.49  fof(f33,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.49    inference(flattening,[],[f32])).
% 7.64/1.49  
% 7.64/1.49  fof(f61,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f33])).
% 7.64/1.49  
% 7.64/1.49  fof(f10,axiom,(
% 7.64/1.49    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 7.64/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f23,plain,(
% 7.64/1.49    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 7.64/1.49    inference(ennf_transformation,[],[f10])).
% 7.64/1.49  
% 7.64/1.49  fof(f51,plain,(
% 7.64/1.49    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f23])).
% 7.64/1.49  
% 7.64/1.49  fof(f65,plain,(
% 7.64/1.49    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 7.64/1.49    inference(cnf_transformation,[],[f41])).
% 7.64/1.49  
% 7.64/1.49  cnf(c_18,negated_conjecture,
% 7.64/1.49      ( v1_relat_1(sK3) ),
% 7.64/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_454,plain,
% 7.64/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_9,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_460,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.64/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_4,plain,
% 7.64/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_465,plain,
% 7.64/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_7,plain,
% 7.64/1.49      ( ~ r2_hidden(X0,X1)
% 7.64/1.49      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_462,plain,
% 7.64/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.64/1.49      | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1211,plain,
% 7.64/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_465,c_462]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1940,plain,
% 7.64/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_460,c_1211]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11,plain,
% 7.64/1.49      ( ~ v1_relat_1(X0)
% 7.64/1.49      | ~ v1_relat_1(X1)
% 7.64/1.49      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_458,plain,
% 7.64/1.49      ( v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top
% 7.64/1.49      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_12,plain,
% 7.64/1.49      ( ~ v1_relat_1(X0)
% 7.64/1.49      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_457,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1204,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_458,c_457]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2975,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1940,c_1204]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11954,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_454,c_2975]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_15,plain,
% 7.64/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_13,plain,
% 7.64/1.49      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 7.64/1.49      | ~ v1_relat_1(X0)
% 7.64/1.49      | ~ v1_relat_1(X1)
% 7.64/1.49      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_456,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.64/1.49      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_860,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 7.64/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_15,c_456]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_16,plain,
% 7.64/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_874,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.64/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_860,c_16]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_35,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.64/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_37,plain,
% 7.64/1.49      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_35]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1016,plain,
% 7.64/1.49      ( ~ r2_hidden(sK0(X0),X0)
% 7.64/1.49      | ~ r1_xboole_0(k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),X1),X0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1408,plain,
% 7.64/1.49      ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 7.64/1.49      | ~ r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_1016]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1410,plain,
% 7.64/1.49      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.64/1.49      | r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1409,plain,
% 7.64/1.49      ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1412,plain,
% 7.64/1.49      ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1579,plain,
% 7.64/1.49      ( v1_relat_1(X0) != iProver_top
% 7.64/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.64/1.49      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_874,c_37,c_1410,c_1412]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1580,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.64/1.49      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(renaming,[status(thm)],[c_1579]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3,plain,
% 7.64/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_466,plain,
% 7.64/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1586,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(forward_subsumption_resolution,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_1580,c_466]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1591,plain,
% 7.64/1.49      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_454,c_1586]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11961,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_11954,c_1591]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_0,plain,
% 7.64/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_468,plain,
% 7.64/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_6,plain,
% 7.64/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_463,plain,
% 7.64/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.64/1.49      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1,plain,
% 7.64/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_467,plain,
% 7.64/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_974,plain,
% 7.64/1.49      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.64/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_463,c_467]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1743,plain,
% 7.64/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_468,c_974]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11962,plain,
% 7.64/1.49      ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_11961,c_2,c_1743]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2974,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_454,c_1204]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11326,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1940,c_2974]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14,plain,
% 7.64/1.49      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 7.64/1.49      | ~ v1_relat_1(X0)
% 7.64/1.49      | ~ v1_relat_1(X1)
% 7.64/1.49      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_455,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 7.64/1.49      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X1) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_635,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 7.64/1.49      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_16,c_455]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_649,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.64/1.49      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_635,c_15]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1349,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.64/1.49      | v1_relat_1(X0) != iProver_top
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(forward_subsumption_resolution,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_649,c_466]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1354,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 7.64/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_454,c_1349]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_36,plain,
% 7.64/1.49      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 7.64/1.49      | v1_relat_1(k1_xboole_0) ),
% 7.64/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1370,plain,
% 7.64/1.49      ( ~ v1_relat_1(k1_xboole_0)
% 7.64/1.49      | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 7.64/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1354]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2223,plain,
% 7.64/1.49      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_1354,c_36,c_1370,c_1408,c_1409]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11328,plain,
% 7.64/1.49      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_11326,c_2223]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_5,plain,
% 7.64/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_464,plain,
% 7.64/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.64/1.49      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1046,plain,
% 7.64/1.49      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.64/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_464,c_467]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2128,plain,
% 7.64/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_468,c_1046]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11329,plain,
% 7.64/1.49      ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_11328,c_2,c_2128]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_17,negated_conjecture,
% 7.64/1.49      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 7.64/1.49      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 7.64/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11347,plain,
% 7.64/1.49      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 7.64/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_11329,c_17]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11348,plain,
% 7.64/1.49      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
% 7.64/1.49      inference(equality_resolution_simp,[status(thm)],[c_11347]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(contradiction,plain,
% 7.64/1.49      ( $false ),
% 7.64/1.49      inference(minisat,[status(thm)],[c_11962,c_11348]) ).
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  ------                               Statistics
% 7.64/1.49  
% 7.64/1.49  ------ Selected
% 7.64/1.49  
% 7.64/1.49  total_time:                             0.541
% 7.64/1.49  
%------------------------------------------------------------------------------
