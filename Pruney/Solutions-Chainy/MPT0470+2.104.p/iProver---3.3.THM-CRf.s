%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:13 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 370 expanded)
%              Number of clauses        :   70 ( 116 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  303 ( 737 expanded)
%              Number of equality atoms :  167 ( 405 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f42])).

fof(f69,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f77,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_590,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_596,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_601,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_598,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1471,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_601,c_598])).

cnf(c_2148,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_1471])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_594,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_593,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1464,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_593])).

cnf(c_3072,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2148,c_1464])).

cnf(c_7916,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_590,c_3072])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_591,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_781,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_591])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_795,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_781,c_19])).

cnf(c_38,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_40,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_1269,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | ~ r1_xboole_0(k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),X1),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1729,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1731,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_1730,plain,
    ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1733,plain,
    ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_1772,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_40,c_1731,c_1733])).

cnf(c_1773,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1772])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_602,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1779,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1773,c_602])).

cnf(c_1784,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_590,c_1779])).

cnf(c_7923,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7916,c_1784])).

cnf(c_5,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_606,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_599,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_605,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1228,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_605])).

cnf(c_1999,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_1228])).

cnf(c_7924,plain,
    ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7923,c_5,c_1999])).

cnf(c_3071,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_1464])).

cnf(c_7343,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2148,c_3071])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_592,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1011,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_592])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_604,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1580,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X0,k1_xboole_0))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_604])).

cnf(c_1347,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_604])).

cnf(c_2402,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1347])).

cnf(c_3974,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_40,c_1731,c_1733,c_2402])).

cnf(c_3975,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3974])).

cnf(c_3981,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_590,c_3975])).

cnf(c_7345,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7343,c_3981])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_600,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1340,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_605])).

cnf(c_2415,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_1340])).

cnf(c_7346,plain,
    ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7345,c_5,c_2415])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7517,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7346,c_20])).

cnf(c_7518,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7924,c_7518])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:55:39 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.99/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/0.95  
% 3.99/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/0.95  
% 3.99/0.95  ------  iProver source info
% 3.99/0.95  
% 3.99/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.99/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/0.95  git: non_committed_changes: false
% 3.99/0.95  git: last_make_outside_of_git: false
% 3.99/0.95  
% 3.99/0.95  ------ 
% 3.99/0.95  
% 3.99/0.95  ------ Input Options
% 3.99/0.95  
% 3.99/0.95  --out_options                           all
% 3.99/0.95  --tptp_safe_out                         true
% 3.99/0.95  --problem_path                          ""
% 3.99/0.95  --include_path                          ""
% 3.99/0.95  --clausifier                            res/vclausify_rel
% 3.99/0.95  --clausifier_options                    --mode clausify
% 3.99/0.95  --stdin                                 false
% 3.99/0.95  --stats_out                             sel
% 3.99/0.95  
% 3.99/0.95  ------ General Options
% 3.99/0.95  
% 3.99/0.95  --fof                                   false
% 3.99/0.95  --time_out_real                         604.99
% 3.99/0.95  --time_out_virtual                      -1.
% 3.99/0.95  --symbol_type_check                     false
% 3.99/0.95  --clausify_out                          false
% 3.99/0.95  --sig_cnt_out                           false
% 3.99/0.95  --trig_cnt_out                          false
% 3.99/0.95  --trig_cnt_out_tolerance                1.
% 3.99/0.95  --trig_cnt_out_sk_spl                   false
% 3.99/0.95  --abstr_cl_out                          false
% 3.99/0.95  
% 3.99/0.95  ------ Global Options
% 3.99/0.95  
% 3.99/0.95  --schedule                              none
% 3.99/0.95  --add_important_lit                     false
% 3.99/0.95  --prop_solver_per_cl                    1000
% 3.99/0.95  --min_unsat_core                        false
% 3.99/0.95  --soft_assumptions                      false
% 3.99/0.95  --soft_lemma_size                       3
% 3.99/0.95  --prop_impl_unit_size                   0
% 3.99/0.95  --prop_impl_unit                        []
% 3.99/0.95  --share_sel_clauses                     true
% 3.99/0.95  --reset_solvers                         false
% 3.99/0.95  --bc_imp_inh                            [conj_cone]
% 3.99/0.95  --conj_cone_tolerance                   3.
% 3.99/0.95  --extra_neg_conj                        none
% 3.99/0.95  --large_theory_mode                     true
% 3.99/0.95  --prolific_symb_bound                   200
% 3.99/0.95  --lt_threshold                          2000
% 3.99/0.95  --clause_weak_htbl                      true
% 3.99/0.95  --gc_record_bc_elim                     false
% 3.99/0.95  
% 3.99/0.95  ------ Preprocessing Options
% 3.99/0.95  
% 3.99/0.95  --preprocessing_flag                    true
% 3.99/0.95  --time_out_prep_mult                    0.1
% 3.99/0.95  --splitting_mode                        input
% 3.99/0.95  --splitting_grd                         true
% 3.99/0.95  --splitting_cvd                         false
% 3.99/0.95  --splitting_cvd_svl                     false
% 3.99/0.95  --splitting_nvd                         32
% 3.99/0.95  --sub_typing                            true
% 3.99/0.95  --prep_gs_sim                           false
% 3.99/0.95  --prep_unflatten                        true
% 3.99/0.95  --prep_res_sim                          true
% 3.99/0.95  --prep_upred                            true
% 3.99/0.95  --prep_sem_filter                       exhaustive
% 3.99/0.95  --prep_sem_filter_out                   false
% 3.99/0.95  --pred_elim                             false
% 3.99/0.95  --res_sim_input                         true
% 3.99/0.95  --eq_ax_congr_red                       true
% 3.99/0.95  --pure_diseq_elim                       true
% 3.99/0.95  --brand_transform                       false
% 3.99/0.95  --non_eq_to_eq                          false
% 3.99/0.95  --prep_def_merge                        true
% 3.99/0.95  --prep_def_merge_prop_impl              false
% 3.99/0.95  --prep_def_merge_mbd                    true
% 3.99/0.95  --prep_def_merge_tr_red                 false
% 3.99/0.95  --prep_def_merge_tr_cl                  false
% 3.99/0.95  --smt_preprocessing                     true
% 3.99/0.95  --smt_ac_axioms                         fast
% 3.99/0.95  --preprocessed_out                      false
% 3.99/0.95  --preprocessed_stats                    false
% 3.99/0.95  
% 3.99/0.95  ------ Abstraction refinement Options
% 3.99/0.95  
% 3.99/0.95  --abstr_ref                             []
% 3.99/0.95  --abstr_ref_prep                        false
% 3.99/0.95  --abstr_ref_until_sat                   false
% 3.99/0.95  --abstr_ref_sig_restrict                funpre
% 3.99/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.95  --abstr_ref_under                       []
% 3.99/0.95  
% 3.99/0.95  ------ SAT Options
% 3.99/0.95  
% 3.99/0.95  --sat_mode                              false
% 3.99/0.95  --sat_fm_restart_options                ""
% 3.99/0.95  --sat_gr_def                            false
% 3.99/0.95  --sat_epr_types                         true
% 3.99/0.95  --sat_non_cyclic_types                  false
% 3.99/0.95  --sat_finite_models                     false
% 3.99/0.95  --sat_fm_lemmas                         false
% 3.99/0.95  --sat_fm_prep                           false
% 3.99/0.95  --sat_fm_uc_incr                        true
% 3.99/0.95  --sat_out_model                         small
% 3.99/0.95  --sat_out_clauses                       false
% 3.99/0.95  
% 3.99/0.95  ------ QBF Options
% 3.99/0.95  
% 3.99/0.95  --qbf_mode                              false
% 3.99/0.95  --qbf_elim_univ                         false
% 3.99/0.95  --qbf_dom_inst                          none
% 3.99/0.95  --qbf_dom_pre_inst                      false
% 3.99/0.95  --qbf_sk_in                             false
% 3.99/0.95  --qbf_pred_elim                         true
% 3.99/0.95  --qbf_split                             512
% 3.99/0.95  
% 3.99/0.95  ------ BMC1 Options
% 3.99/0.95  
% 3.99/0.95  --bmc1_incremental                      false
% 3.99/0.95  --bmc1_axioms                           reachable_all
% 3.99/0.95  --bmc1_min_bound                        0
% 3.99/0.95  --bmc1_max_bound                        -1
% 3.99/0.95  --bmc1_max_bound_default                -1
% 3.99/0.95  --bmc1_symbol_reachability              true
% 3.99/0.95  --bmc1_property_lemmas                  false
% 3.99/0.95  --bmc1_k_induction                      false
% 3.99/0.95  --bmc1_non_equiv_states                 false
% 3.99/0.95  --bmc1_deadlock                         false
% 3.99/0.95  --bmc1_ucm                              false
% 3.99/0.95  --bmc1_add_unsat_core                   none
% 3.99/0.95  --bmc1_unsat_core_children              false
% 3.99/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.95  --bmc1_out_stat                         full
% 3.99/0.95  --bmc1_ground_init                      false
% 3.99/0.95  --bmc1_pre_inst_next_state              false
% 3.99/0.95  --bmc1_pre_inst_state                   false
% 3.99/0.95  --bmc1_pre_inst_reach_state             false
% 3.99/0.95  --bmc1_out_unsat_core                   false
% 3.99/0.95  --bmc1_aig_witness_out                  false
% 3.99/0.95  --bmc1_verbose                          false
% 3.99/0.95  --bmc1_dump_clauses_tptp                false
% 3.99/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.95  --bmc1_dump_file                        -
% 3.99/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.95  --bmc1_ucm_extend_mode                  1
% 3.99/0.95  --bmc1_ucm_init_mode                    2
% 3.99/0.95  --bmc1_ucm_cone_mode                    none
% 3.99/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.95  --bmc1_ucm_relax_model                  4
% 3.99/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.95  --bmc1_ucm_layered_model                none
% 3.99/0.95  --bmc1_ucm_max_lemma_size               10
% 3.99/0.95  
% 3.99/0.95  ------ AIG Options
% 3.99/0.95  
% 3.99/0.95  --aig_mode                              false
% 3.99/0.95  
% 3.99/0.95  ------ Instantiation Options
% 3.99/0.95  
% 3.99/0.95  --instantiation_flag                    true
% 3.99/0.95  --inst_sos_flag                         false
% 3.99/0.95  --inst_sos_phase                        true
% 3.99/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.95  --inst_lit_sel_side                     num_symb
% 3.99/0.95  --inst_solver_per_active                1400
% 3.99/0.95  --inst_solver_calls_frac                1.
% 3.99/0.95  --inst_passive_queue_type               priority_queues
% 3.99/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.95  --inst_passive_queues_freq              [25;2]
% 3.99/0.95  --inst_dismatching                      true
% 3.99/0.95  --inst_eager_unprocessed_to_passive     true
% 3.99/0.95  --inst_prop_sim_given                   true
% 3.99/0.95  --inst_prop_sim_new                     false
% 3.99/0.95  --inst_subs_new                         false
% 3.99/0.95  --inst_eq_res_simp                      false
% 3.99/0.95  --inst_subs_given                       false
% 3.99/0.95  --inst_orphan_elimination               true
% 3.99/0.95  --inst_learning_loop_flag               true
% 3.99/0.95  --inst_learning_start                   3000
% 3.99/0.95  --inst_learning_factor                  2
% 3.99/0.95  --inst_start_prop_sim_after_learn       3
% 3.99/0.95  --inst_sel_renew                        solver
% 3.99/0.95  --inst_lit_activity_flag                true
% 3.99/0.95  --inst_restr_to_given                   false
% 3.99/0.95  --inst_activity_threshold               500
% 3.99/0.95  --inst_out_proof                        true
% 3.99/0.95  
% 3.99/0.95  ------ Resolution Options
% 3.99/0.95  
% 3.99/0.95  --resolution_flag                       true
% 3.99/0.95  --res_lit_sel                           adaptive
% 3.99/0.95  --res_lit_sel_side                      none
% 3.99/0.95  --res_ordering                          kbo
% 3.99/0.95  --res_to_prop_solver                    active
% 3.99/0.95  --res_prop_simpl_new                    false
% 3.99/0.95  --res_prop_simpl_given                  true
% 3.99/0.95  --res_passive_queue_type                priority_queues
% 3.99/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.95  --res_passive_queues_freq               [15;5]
% 3.99/0.95  --res_forward_subs                      full
% 3.99/0.95  --res_backward_subs                     full
% 3.99/0.95  --res_forward_subs_resolution           true
% 3.99/0.95  --res_backward_subs_resolution          true
% 3.99/0.95  --res_orphan_elimination                true
% 3.99/0.95  --res_time_limit                        2.
% 3.99/0.95  --res_out_proof                         true
% 3.99/0.95  
% 3.99/0.95  ------ Superposition Options
% 3.99/0.95  
% 3.99/0.95  --superposition_flag                    true
% 3.99/0.95  --sup_passive_queue_type                priority_queues
% 3.99/0.95  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.95  --sup_passive_queues_freq               [1;4]
% 3.99/0.95  --demod_completeness_check              fast
% 3.99/0.95  --demod_use_ground                      true
% 3.99/0.95  --sup_to_prop_solver                    passive
% 3.99/0.95  --sup_prop_simpl_new                    true
% 3.99/0.95  --sup_prop_simpl_given                  true
% 3.99/0.95  --sup_fun_splitting                     false
% 3.99/0.95  --sup_smt_interval                      50000
% 3.99/0.95  
% 3.99/0.95  ------ Superposition Simplification Setup
% 3.99/0.95  
% 3.99/0.95  --sup_indices_passive                   []
% 3.99/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_full_bw                           [BwDemod]
% 3.99/0.95  --sup_immed_triv                        [TrivRules]
% 3.99/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_immed_bw_main                     []
% 3.99/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.95  
% 3.99/0.95  ------ Combination Options
% 3.99/0.95  
% 3.99/0.95  --comb_res_mult                         3
% 3.99/0.95  --comb_sup_mult                         2
% 3.99/0.95  --comb_inst_mult                        10
% 3.99/0.95  
% 3.99/0.95  ------ Debug Options
% 3.99/0.95  
% 3.99/0.95  --dbg_backtrace                         false
% 3.99/0.95  --dbg_dump_prop_clauses                 false
% 3.99/0.95  --dbg_dump_prop_clauses_file            -
% 3.99/0.95  --dbg_out_stat                          false
% 3.99/0.95  ------ Parsing...
% 3.99/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/0.95  
% 3.99/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.99/0.95  
% 3.99/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/0.95  
% 3.99/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/0.95  ------ Proving...
% 3.99/0.95  ------ Problem Properties 
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  clauses                                 21
% 3.99/0.95  conjectures                             2
% 3.99/0.95  EPR                                     7
% 3.99/0.95  Horn                                    20
% 3.99/0.95  unary                                   8
% 3.99/0.95  binary                                  8
% 3.99/0.95  lits                                    40
% 3.99/0.95  lits eq                                 11
% 3.99/0.95  fd_pure                                 0
% 3.99/0.95  fd_pseudo                               0
% 3.99/0.95  fd_cond                                 1
% 3.99/0.95  fd_pseudo_cond                          1
% 3.99/0.95  AC symbols                              0
% 3.99/0.95  
% 3.99/0.95  ------ Input Options Time Limit: Unbounded
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  ------ 
% 3.99/0.95  Current options:
% 3.99/0.95  ------ 
% 3.99/0.95  
% 3.99/0.95  ------ Input Options
% 3.99/0.95  
% 3.99/0.95  --out_options                           all
% 3.99/0.95  --tptp_safe_out                         true
% 3.99/0.95  --problem_path                          ""
% 3.99/0.95  --include_path                          ""
% 3.99/0.95  --clausifier                            res/vclausify_rel
% 3.99/0.95  --clausifier_options                    --mode clausify
% 3.99/0.95  --stdin                                 false
% 3.99/0.95  --stats_out                             sel
% 3.99/0.95  
% 3.99/0.95  ------ General Options
% 3.99/0.95  
% 3.99/0.95  --fof                                   false
% 3.99/0.95  --time_out_real                         604.99
% 3.99/0.95  --time_out_virtual                      -1.
% 3.99/0.95  --symbol_type_check                     false
% 3.99/0.95  --clausify_out                          false
% 3.99/0.95  --sig_cnt_out                           false
% 3.99/0.95  --trig_cnt_out                          false
% 3.99/0.95  --trig_cnt_out_tolerance                1.
% 3.99/0.95  --trig_cnt_out_sk_spl                   false
% 3.99/0.95  --abstr_cl_out                          false
% 3.99/0.95  
% 3.99/0.95  ------ Global Options
% 3.99/0.95  
% 3.99/0.95  --schedule                              none
% 3.99/0.95  --add_important_lit                     false
% 3.99/0.95  --prop_solver_per_cl                    1000
% 3.99/0.95  --min_unsat_core                        false
% 3.99/0.95  --soft_assumptions                      false
% 3.99/0.95  --soft_lemma_size                       3
% 3.99/0.95  --prop_impl_unit_size                   0
% 3.99/0.95  --prop_impl_unit                        []
% 3.99/0.95  --share_sel_clauses                     true
% 3.99/0.95  --reset_solvers                         false
% 3.99/0.95  --bc_imp_inh                            [conj_cone]
% 3.99/0.95  --conj_cone_tolerance                   3.
% 3.99/0.95  --extra_neg_conj                        none
% 3.99/0.95  --large_theory_mode                     true
% 3.99/0.95  --prolific_symb_bound                   200
% 3.99/0.95  --lt_threshold                          2000
% 3.99/0.95  --clause_weak_htbl                      true
% 3.99/0.95  --gc_record_bc_elim                     false
% 3.99/0.95  
% 3.99/0.95  ------ Preprocessing Options
% 3.99/0.95  
% 3.99/0.95  --preprocessing_flag                    true
% 3.99/0.95  --time_out_prep_mult                    0.1
% 3.99/0.95  --splitting_mode                        input
% 3.99/0.95  --splitting_grd                         true
% 3.99/0.95  --splitting_cvd                         false
% 3.99/0.95  --splitting_cvd_svl                     false
% 3.99/0.95  --splitting_nvd                         32
% 3.99/0.95  --sub_typing                            true
% 3.99/0.95  --prep_gs_sim                           false
% 3.99/0.95  --prep_unflatten                        true
% 3.99/0.95  --prep_res_sim                          true
% 3.99/0.95  --prep_upred                            true
% 3.99/0.95  --prep_sem_filter                       exhaustive
% 3.99/0.95  --prep_sem_filter_out                   false
% 3.99/0.95  --pred_elim                             false
% 3.99/0.95  --res_sim_input                         true
% 3.99/0.95  --eq_ax_congr_red                       true
% 3.99/0.95  --pure_diseq_elim                       true
% 3.99/0.95  --brand_transform                       false
% 3.99/0.95  --non_eq_to_eq                          false
% 3.99/0.95  --prep_def_merge                        true
% 3.99/0.95  --prep_def_merge_prop_impl              false
% 3.99/0.95  --prep_def_merge_mbd                    true
% 3.99/0.95  --prep_def_merge_tr_red                 false
% 3.99/0.95  --prep_def_merge_tr_cl                  false
% 3.99/0.95  --smt_preprocessing                     true
% 3.99/0.95  --smt_ac_axioms                         fast
% 3.99/0.95  --preprocessed_out                      false
% 3.99/0.95  --preprocessed_stats                    false
% 3.99/0.95  
% 3.99/0.95  ------ Abstraction refinement Options
% 3.99/0.95  
% 3.99/0.95  --abstr_ref                             []
% 3.99/0.95  --abstr_ref_prep                        false
% 3.99/0.95  --abstr_ref_until_sat                   false
% 3.99/0.95  --abstr_ref_sig_restrict                funpre
% 3.99/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.95  --abstr_ref_under                       []
% 3.99/0.95  
% 3.99/0.95  ------ SAT Options
% 3.99/0.95  
% 3.99/0.95  --sat_mode                              false
% 3.99/0.95  --sat_fm_restart_options                ""
% 3.99/0.95  --sat_gr_def                            false
% 3.99/0.95  --sat_epr_types                         true
% 3.99/0.95  --sat_non_cyclic_types                  false
% 3.99/0.95  --sat_finite_models                     false
% 3.99/0.95  --sat_fm_lemmas                         false
% 3.99/0.95  --sat_fm_prep                           false
% 3.99/0.95  --sat_fm_uc_incr                        true
% 3.99/0.95  --sat_out_model                         small
% 3.99/0.95  --sat_out_clauses                       false
% 3.99/0.95  
% 3.99/0.95  ------ QBF Options
% 3.99/0.95  
% 3.99/0.95  --qbf_mode                              false
% 3.99/0.95  --qbf_elim_univ                         false
% 3.99/0.95  --qbf_dom_inst                          none
% 3.99/0.95  --qbf_dom_pre_inst                      false
% 3.99/0.95  --qbf_sk_in                             false
% 3.99/0.95  --qbf_pred_elim                         true
% 3.99/0.95  --qbf_split                             512
% 3.99/0.95  
% 3.99/0.95  ------ BMC1 Options
% 3.99/0.95  
% 3.99/0.95  --bmc1_incremental                      false
% 3.99/0.95  --bmc1_axioms                           reachable_all
% 3.99/0.95  --bmc1_min_bound                        0
% 3.99/0.95  --bmc1_max_bound                        -1
% 3.99/0.95  --bmc1_max_bound_default                -1
% 3.99/0.95  --bmc1_symbol_reachability              true
% 3.99/0.95  --bmc1_property_lemmas                  false
% 3.99/0.95  --bmc1_k_induction                      false
% 3.99/0.95  --bmc1_non_equiv_states                 false
% 3.99/0.95  --bmc1_deadlock                         false
% 3.99/0.95  --bmc1_ucm                              false
% 3.99/0.95  --bmc1_add_unsat_core                   none
% 3.99/0.95  --bmc1_unsat_core_children              false
% 3.99/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.95  --bmc1_out_stat                         full
% 3.99/0.95  --bmc1_ground_init                      false
% 3.99/0.95  --bmc1_pre_inst_next_state              false
% 3.99/0.95  --bmc1_pre_inst_state                   false
% 3.99/0.95  --bmc1_pre_inst_reach_state             false
% 3.99/0.95  --bmc1_out_unsat_core                   false
% 3.99/0.95  --bmc1_aig_witness_out                  false
% 3.99/0.95  --bmc1_verbose                          false
% 3.99/0.95  --bmc1_dump_clauses_tptp                false
% 3.99/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.95  --bmc1_dump_file                        -
% 3.99/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.95  --bmc1_ucm_extend_mode                  1
% 3.99/0.95  --bmc1_ucm_init_mode                    2
% 3.99/0.95  --bmc1_ucm_cone_mode                    none
% 3.99/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.95  --bmc1_ucm_relax_model                  4
% 3.99/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.95  --bmc1_ucm_layered_model                none
% 3.99/0.95  --bmc1_ucm_max_lemma_size               10
% 3.99/0.95  
% 3.99/0.95  ------ AIG Options
% 3.99/0.95  
% 3.99/0.95  --aig_mode                              false
% 3.99/0.95  
% 3.99/0.95  ------ Instantiation Options
% 3.99/0.95  
% 3.99/0.95  --instantiation_flag                    true
% 3.99/0.95  --inst_sos_flag                         false
% 3.99/0.95  --inst_sos_phase                        true
% 3.99/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.95  --inst_lit_sel_side                     num_symb
% 3.99/0.95  --inst_solver_per_active                1400
% 3.99/0.95  --inst_solver_calls_frac                1.
% 3.99/0.95  --inst_passive_queue_type               priority_queues
% 3.99/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.95  --inst_passive_queues_freq              [25;2]
% 3.99/0.95  --inst_dismatching                      true
% 3.99/0.95  --inst_eager_unprocessed_to_passive     true
% 3.99/0.95  --inst_prop_sim_given                   true
% 3.99/0.95  --inst_prop_sim_new                     false
% 3.99/0.95  --inst_subs_new                         false
% 3.99/0.95  --inst_eq_res_simp                      false
% 3.99/0.95  --inst_subs_given                       false
% 3.99/0.95  --inst_orphan_elimination               true
% 3.99/0.95  --inst_learning_loop_flag               true
% 3.99/0.95  --inst_learning_start                   3000
% 3.99/0.95  --inst_learning_factor                  2
% 3.99/0.95  --inst_start_prop_sim_after_learn       3
% 3.99/0.95  --inst_sel_renew                        solver
% 3.99/0.95  --inst_lit_activity_flag                true
% 3.99/0.95  --inst_restr_to_given                   false
% 3.99/0.95  --inst_activity_threshold               500
% 3.99/0.95  --inst_out_proof                        true
% 3.99/0.95  
% 3.99/0.95  ------ Resolution Options
% 3.99/0.95  
% 3.99/0.95  --resolution_flag                       true
% 3.99/0.95  --res_lit_sel                           adaptive
% 3.99/0.95  --res_lit_sel_side                      none
% 3.99/0.95  --res_ordering                          kbo
% 3.99/0.95  --res_to_prop_solver                    active
% 3.99/0.95  --res_prop_simpl_new                    false
% 3.99/0.95  --res_prop_simpl_given                  true
% 3.99/0.95  --res_passive_queue_type                priority_queues
% 3.99/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/0.95  --res_passive_queues_freq               [15;5]
% 3.99/0.95  --res_forward_subs                      full
% 3.99/0.95  --res_backward_subs                     full
% 3.99/0.95  --res_forward_subs_resolution           true
% 3.99/0.95  --res_backward_subs_resolution          true
% 3.99/0.95  --res_orphan_elimination                true
% 3.99/0.95  --res_time_limit                        2.
% 3.99/0.95  --res_out_proof                         true
% 3.99/0.95  
% 3.99/0.95  ------ Superposition Options
% 3.99/0.95  
% 3.99/0.95  --superposition_flag                    true
% 3.99/0.95  --sup_passive_queue_type                priority_queues
% 3.99/0.95  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/0.95  --sup_passive_queues_freq               [1;4]
% 3.99/0.95  --demod_completeness_check              fast
% 3.99/0.95  --demod_use_ground                      true
% 3.99/0.95  --sup_to_prop_solver                    passive
% 3.99/0.95  --sup_prop_simpl_new                    true
% 3.99/0.95  --sup_prop_simpl_given                  true
% 3.99/0.95  --sup_fun_splitting                     false
% 3.99/0.95  --sup_smt_interval                      50000
% 3.99/0.95  
% 3.99/0.95  ------ Superposition Simplification Setup
% 3.99/0.95  
% 3.99/0.95  --sup_indices_passive                   []
% 3.99/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_full_bw                           [BwDemod]
% 3.99/0.95  --sup_immed_triv                        [TrivRules]
% 3.99/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_immed_bw_main                     []
% 3.99/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/0.95  
% 3.99/0.95  ------ Combination Options
% 3.99/0.95  
% 3.99/0.95  --comb_res_mult                         3
% 3.99/0.95  --comb_sup_mult                         2
% 3.99/0.95  --comb_inst_mult                        10
% 3.99/0.95  
% 3.99/0.95  ------ Debug Options
% 3.99/0.95  
% 3.99/0.95  --dbg_backtrace                         false
% 3.99/0.95  --dbg_dump_prop_clauses                 false
% 3.99/0.95  --dbg_dump_prop_clauses_file            -
% 3.99/0.95  --dbg_out_stat                          false
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  ------ Proving...
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  % SZS status Theorem for theBenchmark.p
% 3.99/0.95  
% 3.99/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/0.95  
% 3.99/0.95  fof(f21,conjecture,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f22,negated_conjecture,(
% 3.99/0.95    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.99/0.95    inference(negated_conjecture,[],[f21])).
% 3.99/0.95  
% 3.99/0.95  fof(f34,plain,(
% 3.99/0.95    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f22])).
% 3.99/0.95  
% 3.99/0.95  fof(f42,plain,(
% 3.99/0.95    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 3.99/0.95    introduced(choice_axiom,[])).
% 3.99/0.95  
% 3.99/0.95  fof(f43,plain,(
% 3.99/0.95    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 3.99/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f42])).
% 3.99/0.95  
% 3.99/0.95  fof(f69,plain,(
% 3.99/0.95    v1_relat_1(sK3)),
% 3.99/0.95    inference(cnf_transformation,[],[f43])).
% 3.99/0.95  
% 3.99/0.95  fof(f15,axiom,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f27,plain,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 3.99/0.95    inference(ennf_transformation,[],[f15])).
% 3.99/0.95  
% 3.99/0.95  fof(f37,plain,(
% 3.99/0.95    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 3.99/0.95    inference(nnf_transformation,[],[f27])).
% 3.99/0.95  
% 3.99/0.95  fof(f38,plain,(
% 3.99/0.95    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.99/0.95    inference(rectify,[],[f37])).
% 3.99/0.95  
% 3.99/0.95  fof(f40,plain,(
% 3.99/0.95    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 3.99/0.95    introduced(choice_axiom,[])).
% 3.99/0.95  
% 3.99/0.95  fof(f39,plain,(
% 3.99/0.95    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 3.99/0.95    introduced(choice_axiom,[])).
% 3.99/0.95  
% 3.99/0.95  fof(f41,plain,(
% 3.99/0.95    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.99/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).
% 3.99/0.95  
% 3.99/0.95  fof(f61,plain,(
% 3.99/0.95    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f41])).
% 3.99/0.95  
% 3.99/0.95  fof(f6,axiom,(
% 3.99/0.95    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f51,plain,(
% 3.99/0.95    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f6])).
% 3.99/0.95  
% 3.99/0.95  fof(f13,axiom,(
% 3.99/0.95    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f26,plain,(
% 3.99/0.95    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.99/0.95    inference(ennf_transformation,[],[f13])).
% 3.99/0.95  
% 3.99/0.95  fof(f58,plain,(
% 3.99/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f26])).
% 3.99/0.95  
% 3.99/0.95  fof(f7,axiom,(
% 3.99/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f52,plain,(
% 3.99/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f7])).
% 3.99/0.95  
% 3.99/0.95  fof(f8,axiom,(
% 3.99/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f53,plain,(
% 3.99/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f8])).
% 3.99/0.95  
% 3.99/0.95  fof(f9,axiom,(
% 3.99/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f54,plain,(
% 3.99/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f9])).
% 3.99/0.95  
% 3.99/0.95  fof(f10,axiom,(
% 3.99/0.95    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f55,plain,(
% 3.99/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f10])).
% 3.99/0.95  
% 3.99/0.95  fof(f71,plain,(
% 3.99/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.99/0.95    inference(definition_unfolding,[],[f54,f55])).
% 3.99/0.95  
% 3.99/0.95  fof(f72,plain,(
% 3.99/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.99/0.95    inference(definition_unfolding,[],[f53,f71])).
% 3.99/0.95  
% 3.99/0.95  fof(f73,plain,(
% 3.99/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.99/0.95    inference(definition_unfolding,[],[f52,f72])).
% 3.99/0.95  
% 3.99/0.95  fof(f76,plain,(
% 3.99/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.99/0.95    inference(definition_unfolding,[],[f58,f73])).
% 3.99/0.95  
% 3.99/0.95  fof(f16,axiom,(
% 3.99/0.95    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f28,plain,(
% 3.99/0.95    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.99/0.95    inference(ennf_transformation,[],[f16])).
% 3.99/0.95  
% 3.99/0.95  fof(f29,plain,(
% 3.99/0.95    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.99/0.95    inference(flattening,[],[f28])).
% 3.99/0.95  
% 3.99/0.95  fof(f63,plain,(
% 3.99/0.95    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f29])).
% 3.99/0.95  
% 3.99/0.95  fof(f17,axiom,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f30,plain,(
% 3.99/0.95    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f17])).
% 3.99/0.95  
% 3.99/0.95  fof(f64,plain,(
% 3.99/0.95    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f30])).
% 3.99/0.95  
% 3.99/0.95  fof(f14,axiom,(
% 3.99/0.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f59,plain,(
% 3.99/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.99/0.95    inference(cnf_transformation,[],[f14])).
% 3.99/0.95  
% 3.99/0.95  fof(f74,plain,(
% 3.99/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.99/0.95    inference(definition_unfolding,[],[f59,f73])).
% 3.99/0.95  
% 3.99/0.95  fof(f77,plain,(
% 3.99/0.95    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.99/0.95    inference(definition_unfolding,[],[f64,f74])).
% 3.99/0.95  
% 3.99/0.95  fof(f20,axiom,(
% 3.99/0.95    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f68,plain,(
% 3.99/0.95    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.99/0.95    inference(cnf_transformation,[],[f20])).
% 3.99/0.95  
% 3.99/0.95  fof(f19,axiom,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f32,plain,(
% 3.99/0.95    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f19])).
% 3.99/0.95  
% 3.99/0.95  fof(f33,plain,(
% 3.99/0.95    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.99/0.95    inference(flattening,[],[f32])).
% 3.99/0.95  
% 3.99/0.95  fof(f66,plain,(
% 3.99/0.95    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f33])).
% 3.99/0.95  
% 3.99/0.95  fof(f67,plain,(
% 3.99/0.95    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.99/0.95    inference(cnf_transformation,[],[f20])).
% 3.99/0.95  
% 3.99/0.95  fof(f5,axiom,(
% 3.99/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f50,plain,(
% 3.99/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f5])).
% 3.99/0.95  
% 3.99/0.95  fof(f4,axiom,(
% 3.99/0.95    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f49,plain,(
% 3.99/0.95    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f4])).
% 3.99/0.95  
% 3.99/0.95  fof(f75,plain,(
% 3.99/0.95    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.99/0.95    inference(definition_unfolding,[],[f49,f74])).
% 3.99/0.95  
% 3.99/0.95  fof(f1,axiom,(
% 3.99/0.95    v1_xboole_0(k1_xboole_0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f44,plain,(
% 3.99/0.95    v1_xboole_0(k1_xboole_0)),
% 3.99/0.95    inference(cnf_transformation,[],[f1])).
% 3.99/0.95  
% 3.99/0.95  fof(f12,axiom,(
% 3.99/0.95    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f25,plain,(
% 3.99/0.95    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f12])).
% 3.99/0.95  
% 3.99/0.95  fof(f57,plain,(
% 3.99/0.95    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f25])).
% 3.99/0.95  
% 3.99/0.95  fof(f2,axiom,(
% 3.99/0.95    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f23,plain,(
% 3.99/0.95    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f2])).
% 3.99/0.95  
% 3.99/0.95  fof(f45,plain,(
% 3.99/0.95    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f23])).
% 3.99/0.95  
% 3.99/0.95  fof(f18,axiom,(
% 3.99/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f31,plain,(
% 3.99/0.95    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.99/0.95    inference(ennf_transformation,[],[f18])).
% 3.99/0.95  
% 3.99/0.95  fof(f65,plain,(
% 3.99/0.95    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f31])).
% 3.99/0.95  
% 3.99/0.95  fof(f3,axiom,(
% 3.99/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f35,plain,(
% 3.99/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.95    inference(nnf_transformation,[],[f3])).
% 3.99/0.95  
% 3.99/0.95  fof(f36,plain,(
% 3.99/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.95    inference(flattening,[],[f35])).
% 3.99/0.95  
% 3.99/0.95  fof(f48,plain,(
% 3.99/0.95    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f36])).
% 3.99/0.95  
% 3.99/0.95  fof(f11,axiom,(
% 3.99/0.95    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.99/0.95  
% 3.99/0.95  fof(f24,plain,(
% 3.99/0.95    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.99/0.95    inference(ennf_transformation,[],[f11])).
% 3.99/0.95  
% 3.99/0.95  fof(f56,plain,(
% 3.99/0.95    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.99/0.95    inference(cnf_transformation,[],[f24])).
% 3.99/0.95  
% 3.99/0.95  fof(f70,plain,(
% 3.99/0.95    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 3.99/0.95    inference(cnf_transformation,[],[f43])).
% 3.99/0.95  
% 3.99/0.95  cnf(c_21,negated_conjecture,
% 3.99/0.95      ( v1_relat_1(sK3) ),
% 3.99/0.95      inference(cnf_transformation,[],[f69]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_590,plain,
% 3.99/0.95      ( v1_relat_1(sK3) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_12,plain,
% 3.99/0.95      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 3.99/0.95      inference(cnf_transformation,[],[f61]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_596,plain,
% 3.99/0.95      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.99/0.95      | v1_relat_1(X0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7,plain,
% 3.99/0.95      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.99/0.95      inference(cnf_transformation,[],[f51]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_601,plain,
% 3.99/0.95      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_10,plain,
% 3.99/0.95      ( ~ r2_hidden(X0,X1)
% 3.99/0.95      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.99/0.95      inference(cnf_transformation,[],[f76]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_598,plain,
% 3.99/0.95      ( r2_hidden(X0,X1) != iProver_top
% 3.99/0.95      | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1471,plain,
% 3.99/0.95      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_601,c_598]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_2148,plain,
% 3.99/0.95      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_596,c_1471]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_14,plain,
% 3.99/0.95      ( ~ v1_relat_1(X0)
% 3.99/0.95      | ~ v1_relat_1(X1)
% 3.99/0.95      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.99/0.95      inference(cnf_transformation,[],[f63]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_594,plain,
% 3.99/0.95      ( v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(X1) != iProver_top
% 3.99/0.95      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_15,plain,
% 3.99/0.95      ( ~ v1_relat_1(X0)
% 3.99/0.95      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.99/0.95      inference(cnf_transformation,[],[f77]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_593,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1464,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_594,c_593]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_3072,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_2148,c_1464]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7916,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_590,c_3072]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_18,plain,
% 3.99/0.95      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.95      inference(cnf_transformation,[],[f68]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_17,plain,
% 3.99/0.95      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.99/0.95      | ~ v1_relat_1(X0)
% 3.99/0.95      | ~ v1_relat_1(X1)
% 3.99/0.95      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.99/0.95      inference(cnf_transformation,[],[f66]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_591,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.99/0.95      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_781,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.99/0.95      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_18,c_591]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_19,plain,
% 3.99/0.95      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.95      inference(cnf_transformation,[],[f67]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_795,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.99/0.95      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(light_normalisation,[status(thm)],[c_781,c_19]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_38,plain,
% 3.99/0.95      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.99/0.95      | v1_relat_1(X0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_40,plain,
% 3.99/0.95      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.99/0.95      inference(instantiation,[status(thm)],[c_38]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1269,plain,
% 3.99/0.95      ( ~ r2_hidden(sK0(X0),X0)
% 3.99/0.95      | ~ r1_xboole_0(k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),X1),X0) ),
% 3.99/0.95      inference(instantiation,[status(thm)],[c_10]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1729,plain,
% 3.99/0.95      ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 3.99/0.95      | ~ r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
% 3.99/0.95      inference(instantiation,[status(thm)],[c_1269]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1731,plain,
% 3.99/0.95      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top
% 3.99/0.95      | r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_1729]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1730,plain,
% 3.99/0.95      ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) ),
% 3.99/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1733,plain,
% 3.99/0.95      ( r1_xboole_0(k4_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_1730]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1772,plain,
% 3.99/0.95      ( v1_relat_1(X0) != iProver_top
% 3.99/0.95      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.99/0.95      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.99/0.95      inference(global_propositional_subsumption,
% 3.99/0.95                [status(thm)],
% 3.99/0.95                [c_795,c_40,c_1731,c_1733]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1773,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.99/0.95      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(renaming,[status(thm)],[c_1772]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_6,plain,
% 3.99/0.95      ( r1_tarski(k1_xboole_0,X0) ),
% 3.99/0.95      inference(cnf_transformation,[],[f50]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_602,plain,
% 3.99/0.95      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1779,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(forward_subsumption_resolution,
% 3.99/0.95                [status(thm)],
% 3.99/0.95                [c_1773,c_602]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1784,plain,
% 3.99/0.95      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_590,c_1779]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7923,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 3.99/0.95      inference(light_normalisation,[status(thm)],[c_7916,c_1784]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_5,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.99/0.95      inference(cnf_transformation,[],[f75]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_0,plain,
% 3.99/0.95      ( v1_xboole_0(k1_xboole_0) ),
% 3.99/0.95      inference(cnf_transformation,[],[f44]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_606,plain,
% 3.99/0.95      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_9,plain,
% 3.99/0.95      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.99/0.95      inference(cnf_transformation,[],[f57]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_599,plain,
% 3.99/0.95      ( v1_xboole_0(X0) != iProver_top
% 3.99/0.95      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1,plain,
% 3.99/0.95      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.99/0.95      inference(cnf_transformation,[],[f45]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_605,plain,
% 3.99/0.95      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1228,plain,
% 3.99/0.95      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.99/0.95      | v1_xboole_0(X0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_599,c_605]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1999,plain,
% 3.99/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_606,c_1228]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7924,plain,
% 3.99/0.95      ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.99/0.95      inference(demodulation,[status(thm)],[c_7923,c_5,c_1999]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_3071,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_590,c_1464]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7343,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_2148,c_3071]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_16,plain,
% 3.99/0.95      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.99/0.95      | ~ v1_relat_1(X0)
% 3.99/0.95      | ~ v1_relat_1(X1) ),
% 3.99/0.95      inference(cnf_transformation,[],[f65]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_592,plain,
% 3.99/0.95      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1011,plain,
% 3.99/0.95      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_18,c_592]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_2,plain,
% 3.99/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.99/0.95      inference(cnf_transformation,[],[f48]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_604,plain,
% 3.99/0.95      ( X0 = X1
% 3.99/0.95      | r1_tarski(X0,X1) != iProver_top
% 3.99/0.95      | r1_tarski(X1,X0) != iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1580,plain,
% 3.99/0.95      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.99/0.95      | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X0,k1_xboole_0))) != iProver_top
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_1011,c_604]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1347,plain,
% 3.99/0.95      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_602,c_604]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_2402,plain,
% 3.99/0.95      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.99/0.95      | v1_relat_1(X0) != iProver_top
% 3.99/0.95      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_1011,c_1347]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_3974,plain,
% 3.99/0.95      ( v1_relat_1(X0) != iProver_top
% 3.99/0.95      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.99/0.95      inference(global_propositional_subsumption,
% 3.99/0.95                [status(thm)],
% 3.99/0.95                [c_1580,c_40,c_1731,c_1733,c_2402]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_3975,plain,
% 3.99/0.95      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.99/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.99/0.95      inference(renaming,[status(thm)],[c_3974]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_3981,plain,
% 3.99/0.95      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_590,c_3975]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7345,plain,
% 3.99/0.95      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 3.99/0.95      inference(light_normalisation,[status(thm)],[c_7343,c_3981]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_8,plain,
% 3.99/0.95      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.99/0.95      inference(cnf_transformation,[],[f56]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_600,plain,
% 3.99/0.95      ( v1_xboole_0(X0) != iProver_top
% 3.99/0.95      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.99/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_1340,plain,
% 3.99/0.95      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.99/0.95      | v1_xboole_0(X1) != iProver_top ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_600,c_605]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_2415,plain,
% 3.99/0.95      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.95      inference(superposition,[status(thm)],[c_606,c_1340]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7346,plain,
% 3.99/0.95      ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 3.99/0.95      inference(demodulation,[status(thm)],[c_7345,c_5,c_2415]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_20,negated_conjecture,
% 3.99/0.95      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 3.99/0.95      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 3.99/0.95      inference(cnf_transformation,[],[f70]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7517,plain,
% 3.99/0.95      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 3.99/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 3.99/0.95      inference(demodulation,[status(thm)],[c_7346,c_20]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(c_7518,plain,
% 3.99/0.95      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
% 3.99/0.95      inference(equality_resolution_simp,[status(thm)],[c_7517]) ).
% 3.99/0.95  
% 3.99/0.95  cnf(contradiction,plain,
% 3.99/0.95      ( $false ),
% 3.99/0.95      inference(minisat,[status(thm)],[c_7924,c_7518]) ).
% 3.99/0.95  
% 3.99/0.95  
% 3.99/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/0.95  
% 3.99/0.95  ------                               Statistics
% 3.99/0.95  
% 3.99/0.95  ------ Selected
% 3.99/0.95  
% 3.99/0.95  total_time:                             0.326
% 3.99/0.95  
%------------------------------------------------------------------------------
