%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:55 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 790 expanded)
%              Number of clauses        :   97 ( 323 expanded)
%              Number of leaves         :   27 ( 176 expanded)
%              Depth                    :   21
%              Number of atoms          :  392 (1897 expanded)
%              Number of equality atoms :  217 ( 870 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(f29,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f42])).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f80,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f69,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_489,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_497,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_494,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_957,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_494])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_493,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_492,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1257,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_493,c_492])).

cnf(c_2668,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_1257])).

cnf(c_12800,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k2_relat_1(k5_relat_1(sK2,k1_xboole_0))))) = k5_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_489,c_2668])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_490,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_661,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_490])).

cnf(c_35,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_37,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_48,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1371,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_37,c_48])).

cnf(c_1372,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1371])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_496,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1378,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X0,k1_xboole_0))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_496])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_499,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_501,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1137,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_501])).

cnf(c_1592,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_496])).

cnf(c_1704,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1592])).

cnf(c_2009,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1378,c_48,c_1704])).

cnf(c_2017,plain,
    ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_489,c_2009])).

cnf(c_12824,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12800,c_2017])).

cnf(c_9,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12825,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12824,c_9,c_10])).

cnf(c_2667,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2))))) = k5_relat_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_1257])).

cnf(c_12085,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_957,c_2667])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_491,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_900,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_491])).

cnf(c_1463,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_37,c_48])).

cnf(c_1464,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1463])).

cnf(c_1470,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,X0))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_496])).

cnf(c_1705,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1592])).

cnf(c_2498,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1470,c_48,c_1705])).

cnf(c_2506,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_489,c_2498])).

cnf(c_12104,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_12085,c_2506])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12105,plain,
    ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12104,c_9,c_11])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_223,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3538,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_227,c_223])).

cnf(c_6666,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3538,c_18])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_498,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1377,plain,
    ( r2_hidden(X0,k2_relat_1(k5_relat_1(X1,k1_xboole_0))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_498])).

cnf(c_1758,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
    | r2_hidden(sK1(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_1377])).

cnf(c_5506,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_501])).

cnf(c_5640,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5506,c_48])).

cnf(c_5641,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5640])).

cnf(c_5646,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_5641])).

cnf(c_5688,plain,
    ( r1_tarski(k1_xboole_0,X0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5646])).

cnf(c_7338,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6666,c_21,c_5688])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2578,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_224,c_18])).

cnf(c_2580,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_224,c_223])).

cnf(c_3764,plain,
    ( X0 = k2_relat_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2578,c_2580])).

cnf(c_6703,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3538,c_3764])).

cnf(c_7351,plain,
    ( r1_tarski(X0,X1)
    | X0 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7338,c_6703])).

cnf(c_8002,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),X1) ),
    inference(resolution,[status(thm)],[c_7351,c_11])).

cnf(c_2996,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2580,c_11])).

cnf(c_3150,plain,
    ( X0 != k2_zfmisc_1(k1_xboole_0,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2996,c_224])).

cnf(c_4463,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_3150,c_6])).

cnf(c_8657,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | k1_xboole_0 = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8002,c_4463])).

cnf(c_912,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_11080,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_8657,c_912])).

cnf(c_8010,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_7351,c_223])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1518,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK2,k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_8021,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8010,c_1518])).

cnf(c_11096,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK2)) ),
    inference(resolution,[status(thm)],[c_11080,c_8021])).

cnf(c_225,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1663,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK2))
    | k5_relat_1(k1_xboole_0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1665,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1129,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | k5_relat_1(sK2,k1_xboole_0) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_1131,plain,
    ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k5_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12825,c_12105,c_11096,c_1665,c_1131,c_5,c_42,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:06:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.99  
% 3.87/0.99  ------  iProver source info
% 3.87/0.99  
% 3.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.99  git: non_committed_changes: false
% 3.87/0.99  git: last_make_outside_of_git: false
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  ------ Input Options
% 3.87/0.99  
% 3.87/0.99  --out_options                           all
% 3.87/0.99  --tptp_safe_out                         true
% 3.87/0.99  --problem_path                          ""
% 3.87/0.99  --include_path                          ""
% 3.87/0.99  --clausifier                            res/vclausify_rel
% 3.87/0.99  --clausifier_options                    --mode clausify
% 3.87/0.99  --stdin                                 false
% 3.87/0.99  --stats_out                             sel
% 3.87/0.99  
% 3.87/0.99  ------ General Options
% 3.87/0.99  
% 3.87/0.99  --fof                                   false
% 3.87/0.99  --time_out_real                         604.99
% 3.87/0.99  --time_out_virtual                      -1.
% 3.87/0.99  --symbol_type_check                     false
% 3.87/0.99  --clausify_out                          false
% 3.87/0.99  --sig_cnt_out                           false
% 3.87/0.99  --trig_cnt_out                          false
% 3.87/0.99  --trig_cnt_out_tolerance                1.
% 3.87/0.99  --trig_cnt_out_sk_spl                   false
% 3.87/0.99  --abstr_cl_out                          false
% 3.87/0.99  
% 3.87/0.99  ------ Global Options
% 3.87/0.99  
% 3.87/0.99  --schedule                              none
% 3.87/0.99  --add_important_lit                     false
% 3.87/0.99  --prop_solver_per_cl                    1000
% 3.87/0.99  --min_unsat_core                        false
% 3.87/0.99  --soft_assumptions                      false
% 3.87/0.99  --soft_lemma_size                       3
% 3.87/0.99  --prop_impl_unit_size                   0
% 3.87/0.99  --prop_impl_unit                        []
% 3.87/0.99  --share_sel_clauses                     true
% 3.87/0.99  --reset_solvers                         false
% 3.87/0.99  --bc_imp_inh                            [conj_cone]
% 3.87/0.99  --conj_cone_tolerance                   3.
% 3.87/0.99  --extra_neg_conj                        none
% 3.87/0.99  --large_theory_mode                     true
% 3.87/0.99  --prolific_symb_bound                   200
% 3.87/0.99  --lt_threshold                          2000
% 3.87/0.99  --clause_weak_htbl                      true
% 3.87/0.99  --gc_record_bc_elim                     false
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing Options
% 3.87/0.99  
% 3.87/0.99  --preprocessing_flag                    true
% 3.87/0.99  --time_out_prep_mult                    0.1
% 3.87/0.99  --splitting_mode                        input
% 3.87/0.99  --splitting_grd                         true
% 3.87/0.99  --splitting_cvd                         false
% 3.87/0.99  --splitting_cvd_svl                     false
% 3.87/0.99  --splitting_nvd                         32
% 3.87/0.99  --sub_typing                            true
% 3.87/0.99  --prep_gs_sim                           false
% 3.87/0.99  --prep_unflatten                        true
% 3.87/0.99  --prep_res_sim                          true
% 3.87/0.99  --prep_upred                            true
% 3.87/0.99  --prep_sem_filter                       exhaustive
% 3.87/0.99  --prep_sem_filter_out                   false
% 3.87/0.99  --pred_elim                             false
% 3.87/0.99  --res_sim_input                         true
% 3.87/0.99  --eq_ax_congr_red                       true
% 3.87/0.99  --pure_diseq_elim                       true
% 3.87/0.99  --brand_transform                       false
% 3.87/0.99  --non_eq_to_eq                          false
% 3.87/0.99  --prep_def_merge                        true
% 3.87/0.99  --prep_def_merge_prop_impl              false
% 3.87/0.99  --prep_def_merge_mbd                    true
% 3.87/0.99  --prep_def_merge_tr_red                 false
% 3.87/0.99  --prep_def_merge_tr_cl                  false
% 3.87/0.99  --smt_preprocessing                     true
% 3.87/0.99  --smt_ac_axioms                         fast
% 3.87/0.99  --preprocessed_out                      false
% 3.87/0.99  --preprocessed_stats                    false
% 3.87/0.99  
% 3.87/0.99  ------ Abstraction refinement Options
% 3.87/0.99  
% 3.87/0.99  --abstr_ref                             []
% 3.87/0.99  --abstr_ref_prep                        false
% 3.87/0.99  --abstr_ref_until_sat                   false
% 3.87/0.99  --abstr_ref_sig_restrict                funpre
% 3.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.99  --abstr_ref_under                       []
% 3.87/0.99  
% 3.87/0.99  ------ SAT Options
% 3.87/0.99  
% 3.87/0.99  --sat_mode                              false
% 3.87/0.99  --sat_fm_restart_options                ""
% 3.87/0.99  --sat_gr_def                            false
% 3.87/0.99  --sat_epr_types                         true
% 3.87/0.99  --sat_non_cyclic_types                  false
% 3.87/0.99  --sat_finite_models                     false
% 3.87/0.99  --sat_fm_lemmas                         false
% 3.87/0.99  --sat_fm_prep                           false
% 3.87/0.99  --sat_fm_uc_incr                        true
% 3.87/0.99  --sat_out_model                         small
% 3.87/0.99  --sat_out_clauses                       false
% 3.87/0.99  
% 3.87/0.99  ------ QBF Options
% 3.87/0.99  
% 3.87/0.99  --qbf_mode                              false
% 3.87/0.99  --qbf_elim_univ                         false
% 3.87/0.99  --qbf_dom_inst                          none
% 3.87/0.99  --qbf_dom_pre_inst                      false
% 3.87/0.99  --qbf_sk_in                             false
% 3.87/0.99  --qbf_pred_elim                         true
% 3.87/0.99  --qbf_split                             512
% 3.87/0.99  
% 3.87/0.99  ------ BMC1 Options
% 3.87/0.99  
% 3.87/0.99  --bmc1_incremental                      false
% 3.87/0.99  --bmc1_axioms                           reachable_all
% 3.87/0.99  --bmc1_min_bound                        0
% 3.87/0.99  --bmc1_max_bound                        -1
% 3.87/0.99  --bmc1_max_bound_default                -1
% 3.87/0.99  --bmc1_symbol_reachability              true
% 3.87/0.99  --bmc1_property_lemmas                  false
% 3.87/0.99  --bmc1_k_induction                      false
% 3.87/0.99  --bmc1_non_equiv_states                 false
% 3.87/0.99  --bmc1_deadlock                         false
% 3.87/0.99  --bmc1_ucm                              false
% 3.87/0.99  --bmc1_add_unsat_core                   none
% 3.87/0.99  --bmc1_unsat_core_children              false
% 3.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.99  --bmc1_out_stat                         full
% 3.87/0.99  --bmc1_ground_init                      false
% 3.87/0.99  --bmc1_pre_inst_next_state              false
% 3.87/0.99  --bmc1_pre_inst_state                   false
% 3.87/0.99  --bmc1_pre_inst_reach_state             false
% 3.87/0.99  --bmc1_out_unsat_core                   false
% 3.87/0.99  --bmc1_aig_witness_out                  false
% 3.87/0.99  --bmc1_verbose                          false
% 3.87/0.99  --bmc1_dump_clauses_tptp                false
% 3.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.99  --bmc1_dump_file                        -
% 3.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.99  --bmc1_ucm_extend_mode                  1
% 3.87/0.99  --bmc1_ucm_init_mode                    2
% 3.87/0.99  --bmc1_ucm_cone_mode                    none
% 3.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.99  --bmc1_ucm_relax_model                  4
% 3.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.99  --bmc1_ucm_layered_model                none
% 3.87/0.99  --bmc1_ucm_max_lemma_size               10
% 3.87/0.99  
% 3.87/0.99  ------ AIG Options
% 3.87/0.99  
% 3.87/0.99  --aig_mode                              false
% 3.87/0.99  
% 3.87/0.99  ------ Instantiation Options
% 3.87/0.99  
% 3.87/0.99  --instantiation_flag                    true
% 3.87/0.99  --inst_sos_flag                         false
% 3.87/0.99  --inst_sos_phase                        true
% 3.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel_side                     num_symb
% 3.87/0.99  --inst_solver_per_active                1400
% 3.87/0.99  --inst_solver_calls_frac                1.
% 3.87/0.99  --inst_passive_queue_type               priority_queues
% 3.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.99  --inst_passive_queues_freq              [25;2]
% 3.87/0.99  --inst_dismatching                      true
% 3.87/0.99  --inst_eager_unprocessed_to_passive     true
% 3.87/0.99  --inst_prop_sim_given                   true
% 3.87/0.99  --inst_prop_sim_new                     false
% 3.87/0.99  --inst_subs_new                         false
% 3.87/0.99  --inst_eq_res_simp                      false
% 3.87/0.99  --inst_subs_given                       false
% 3.87/0.99  --inst_orphan_elimination               true
% 3.87/0.99  --inst_learning_loop_flag               true
% 3.87/0.99  --inst_learning_start                   3000
% 3.87/0.99  --inst_learning_factor                  2
% 3.87/0.99  --inst_start_prop_sim_after_learn       3
% 3.87/0.99  --inst_sel_renew                        solver
% 3.87/0.99  --inst_lit_activity_flag                true
% 3.87/0.99  --inst_restr_to_given                   false
% 3.87/0.99  --inst_activity_threshold               500
% 3.87/0.99  --inst_out_proof                        true
% 3.87/0.99  
% 3.87/0.99  ------ Resolution Options
% 3.87/0.99  
% 3.87/0.99  --resolution_flag                       true
% 3.87/0.99  --res_lit_sel                           adaptive
% 3.87/0.99  --res_lit_sel_side                      none
% 3.87/0.99  --res_ordering                          kbo
% 3.87/0.99  --res_to_prop_solver                    active
% 3.87/0.99  --res_prop_simpl_new                    false
% 3.87/0.99  --res_prop_simpl_given                  true
% 3.87/0.99  --res_passive_queue_type                priority_queues
% 3.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.99  --res_passive_queues_freq               [15;5]
% 3.87/0.99  --res_forward_subs                      full
% 3.87/0.99  --res_backward_subs                     full
% 3.87/0.99  --res_forward_subs_resolution           true
% 3.87/0.99  --res_backward_subs_resolution          true
% 3.87/0.99  --res_orphan_elimination                true
% 3.87/0.99  --res_time_limit                        2.
% 3.87/0.99  --res_out_proof                         true
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Options
% 3.87/0.99  
% 3.87/0.99  --superposition_flag                    true
% 3.87/0.99  --sup_passive_queue_type                priority_queues
% 3.87/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.99  --sup_passive_queues_freq               [1;4]
% 3.87/0.99  --demod_completeness_check              fast
% 3.87/0.99  --demod_use_ground                      true
% 3.87/0.99  --sup_to_prop_solver                    passive
% 3.87/0.99  --sup_prop_simpl_new                    true
% 3.87/0.99  --sup_prop_simpl_given                  true
% 3.87/0.99  --sup_fun_splitting                     false
% 3.87/0.99  --sup_smt_interval                      50000
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Simplification Setup
% 3.87/0.99  
% 3.87/0.99  --sup_indices_passive                   []
% 3.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_full_bw                           [BwDemod]
% 3.87/0.99  --sup_immed_triv                        [TrivRules]
% 3.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_immed_bw_main                     []
% 3.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/0.99  
% 3.87/0.99  ------ Combination Options
% 3.87/0.99  
% 3.87/0.99  --comb_res_mult                         3
% 3.87/0.99  --comb_sup_mult                         2
% 3.87/0.99  --comb_inst_mult                        10
% 3.87/0.99  
% 3.87/0.99  ------ Debug Options
% 3.87/0.99  
% 3.87/0.99  --dbg_backtrace                         false
% 3.87/0.99  --dbg_dump_prop_clauses                 false
% 3.87/0.99  --dbg_dump_prop_clauses_file            -
% 3.87/0.99  --dbg_out_stat                          false
% 3.87/0.99  ------ Parsing...
% 3.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.99  ------ Proving...
% 3.87/0.99  ------ Problem Properties 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  clauses                                 21
% 3.87/0.99  conjectures                             2
% 3.87/0.99  EPR                                     7
% 3.87/0.99  Horn                                    18
% 3.87/0.99  unary                                   8
% 3.87/0.99  binary                                  7
% 3.87/0.99  lits                                    40
% 3.87/0.99  lits eq                                 12
% 3.87/0.99  fd_pure                                 0
% 3.87/0.99  fd_pseudo                               0
% 3.87/0.99  fd_cond                                 1
% 3.87/0.99  fd_pseudo_cond                          1
% 3.87/0.99  AC symbols                              0
% 3.87/0.99  
% 3.87/0.99  ------ Input Options Time Limit: Unbounded
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  Current options:
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  ------ Input Options
% 3.87/0.99  
% 3.87/0.99  --out_options                           all
% 3.87/0.99  --tptp_safe_out                         true
% 3.87/0.99  --problem_path                          ""
% 3.87/0.99  --include_path                          ""
% 3.87/0.99  --clausifier                            res/vclausify_rel
% 3.87/0.99  --clausifier_options                    --mode clausify
% 3.87/0.99  --stdin                                 false
% 3.87/0.99  --stats_out                             sel
% 3.87/0.99  
% 3.87/0.99  ------ General Options
% 3.87/0.99  
% 3.87/0.99  --fof                                   false
% 3.87/0.99  --time_out_real                         604.99
% 3.87/0.99  --time_out_virtual                      -1.
% 3.87/0.99  --symbol_type_check                     false
% 3.87/0.99  --clausify_out                          false
% 3.87/0.99  --sig_cnt_out                           false
% 3.87/0.99  --trig_cnt_out                          false
% 3.87/0.99  --trig_cnt_out_tolerance                1.
% 3.87/0.99  --trig_cnt_out_sk_spl                   false
% 3.87/0.99  --abstr_cl_out                          false
% 3.87/0.99  
% 3.87/0.99  ------ Global Options
% 3.87/0.99  
% 3.87/0.99  --schedule                              none
% 3.87/0.99  --add_important_lit                     false
% 3.87/0.99  --prop_solver_per_cl                    1000
% 3.87/0.99  --min_unsat_core                        false
% 3.87/0.99  --soft_assumptions                      false
% 3.87/0.99  --soft_lemma_size                       3
% 3.87/0.99  --prop_impl_unit_size                   0
% 3.87/0.99  --prop_impl_unit                        []
% 3.87/0.99  --share_sel_clauses                     true
% 3.87/0.99  --reset_solvers                         false
% 3.87/0.99  --bc_imp_inh                            [conj_cone]
% 3.87/0.99  --conj_cone_tolerance                   3.
% 3.87/0.99  --extra_neg_conj                        none
% 3.87/0.99  --large_theory_mode                     true
% 3.87/0.99  --prolific_symb_bound                   200
% 3.87/0.99  --lt_threshold                          2000
% 3.87/0.99  --clause_weak_htbl                      true
% 3.87/0.99  --gc_record_bc_elim                     false
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing Options
% 3.87/0.99  
% 3.87/0.99  --preprocessing_flag                    true
% 3.87/0.99  --time_out_prep_mult                    0.1
% 3.87/0.99  --splitting_mode                        input
% 3.87/0.99  --splitting_grd                         true
% 3.87/0.99  --splitting_cvd                         false
% 3.87/0.99  --splitting_cvd_svl                     false
% 3.87/0.99  --splitting_nvd                         32
% 3.87/0.99  --sub_typing                            true
% 3.87/0.99  --prep_gs_sim                           false
% 3.87/0.99  --prep_unflatten                        true
% 3.87/0.99  --prep_res_sim                          true
% 3.87/0.99  --prep_upred                            true
% 3.87/0.99  --prep_sem_filter                       exhaustive
% 3.87/0.99  --prep_sem_filter_out                   false
% 3.87/0.99  --pred_elim                             false
% 3.87/0.99  --res_sim_input                         true
% 3.87/0.99  --eq_ax_congr_red                       true
% 3.87/0.99  --pure_diseq_elim                       true
% 3.87/0.99  --brand_transform                       false
% 3.87/0.99  --non_eq_to_eq                          false
% 3.87/0.99  --prep_def_merge                        true
% 3.87/0.99  --prep_def_merge_prop_impl              false
% 3.87/0.99  --prep_def_merge_mbd                    true
% 3.87/0.99  --prep_def_merge_tr_red                 false
% 3.87/0.99  --prep_def_merge_tr_cl                  false
% 3.87/0.99  --smt_preprocessing                     true
% 3.87/0.99  --smt_ac_axioms                         fast
% 3.87/0.99  --preprocessed_out                      false
% 3.87/0.99  --preprocessed_stats                    false
% 3.87/0.99  
% 3.87/0.99  ------ Abstraction refinement Options
% 3.87/0.99  
% 3.87/0.99  --abstr_ref                             []
% 3.87/0.99  --abstr_ref_prep                        false
% 3.87/0.99  --abstr_ref_until_sat                   false
% 3.87/0.99  --abstr_ref_sig_restrict                funpre
% 3.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.99  --abstr_ref_under                       []
% 3.87/0.99  
% 3.87/0.99  ------ SAT Options
% 3.87/0.99  
% 3.87/0.99  --sat_mode                              false
% 3.87/0.99  --sat_fm_restart_options                ""
% 3.87/0.99  --sat_gr_def                            false
% 3.87/0.99  --sat_epr_types                         true
% 3.87/0.99  --sat_non_cyclic_types                  false
% 3.87/0.99  --sat_finite_models                     false
% 3.87/0.99  --sat_fm_lemmas                         false
% 3.87/0.99  --sat_fm_prep                           false
% 3.87/0.99  --sat_fm_uc_incr                        true
% 3.87/0.99  --sat_out_model                         small
% 3.87/0.99  --sat_out_clauses                       false
% 3.87/0.99  
% 3.87/0.99  ------ QBF Options
% 3.87/0.99  
% 3.87/0.99  --qbf_mode                              false
% 3.87/0.99  --qbf_elim_univ                         false
% 3.87/0.99  --qbf_dom_inst                          none
% 3.87/0.99  --qbf_dom_pre_inst                      false
% 3.87/0.99  --qbf_sk_in                             false
% 3.87/0.99  --qbf_pred_elim                         true
% 3.87/0.99  --qbf_split                             512
% 3.87/0.99  
% 3.87/0.99  ------ BMC1 Options
% 3.87/0.99  
% 3.87/0.99  --bmc1_incremental                      false
% 3.87/0.99  --bmc1_axioms                           reachable_all
% 3.87/0.99  --bmc1_min_bound                        0
% 3.87/0.99  --bmc1_max_bound                        -1
% 3.87/0.99  --bmc1_max_bound_default                -1
% 3.87/0.99  --bmc1_symbol_reachability              true
% 3.87/0.99  --bmc1_property_lemmas                  false
% 3.87/0.99  --bmc1_k_induction                      false
% 3.87/0.99  --bmc1_non_equiv_states                 false
% 3.87/0.99  --bmc1_deadlock                         false
% 3.87/0.99  --bmc1_ucm                              false
% 3.87/0.99  --bmc1_add_unsat_core                   none
% 3.87/0.99  --bmc1_unsat_core_children              false
% 3.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.99  --bmc1_out_stat                         full
% 3.87/0.99  --bmc1_ground_init                      false
% 3.87/0.99  --bmc1_pre_inst_next_state              false
% 3.87/0.99  --bmc1_pre_inst_state                   false
% 3.87/0.99  --bmc1_pre_inst_reach_state             false
% 3.87/0.99  --bmc1_out_unsat_core                   false
% 3.87/0.99  --bmc1_aig_witness_out                  false
% 3.87/0.99  --bmc1_verbose                          false
% 3.87/0.99  --bmc1_dump_clauses_tptp                false
% 3.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.99  --bmc1_dump_file                        -
% 3.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.99  --bmc1_ucm_extend_mode                  1
% 3.87/0.99  --bmc1_ucm_init_mode                    2
% 3.87/0.99  --bmc1_ucm_cone_mode                    none
% 3.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.99  --bmc1_ucm_relax_model                  4
% 3.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.99  --bmc1_ucm_layered_model                none
% 3.87/0.99  --bmc1_ucm_max_lemma_size               10
% 3.87/0.99  
% 3.87/0.99  ------ AIG Options
% 3.87/0.99  
% 3.87/0.99  --aig_mode                              false
% 3.87/0.99  
% 3.87/0.99  ------ Instantiation Options
% 3.87/0.99  
% 3.87/0.99  --instantiation_flag                    true
% 3.87/0.99  --inst_sos_flag                         false
% 3.87/0.99  --inst_sos_phase                        true
% 3.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel_side                     num_symb
% 3.87/0.99  --inst_solver_per_active                1400
% 3.87/0.99  --inst_solver_calls_frac                1.
% 3.87/0.99  --inst_passive_queue_type               priority_queues
% 3.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.99  --inst_passive_queues_freq              [25;2]
% 3.87/0.99  --inst_dismatching                      true
% 3.87/0.99  --inst_eager_unprocessed_to_passive     true
% 3.87/0.99  --inst_prop_sim_given                   true
% 3.87/0.99  --inst_prop_sim_new                     false
% 3.87/0.99  --inst_subs_new                         false
% 3.87/0.99  --inst_eq_res_simp                      false
% 3.87/0.99  --inst_subs_given                       false
% 3.87/0.99  --inst_orphan_elimination               true
% 3.87/0.99  --inst_learning_loop_flag               true
% 3.87/0.99  --inst_learning_start                   3000
% 3.87/0.99  --inst_learning_factor                  2
% 3.87/0.99  --inst_start_prop_sim_after_learn       3
% 3.87/0.99  --inst_sel_renew                        solver
% 3.87/0.99  --inst_lit_activity_flag                true
% 3.87/0.99  --inst_restr_to_given                   false
% 3.87/0.99  --inst_activity_threshold               500
% 3.87/0.99  --inst_out_proof                        true
% 3.87/0.99  
% 3.87/0.99  ------ Resolution Options
% 3.87/0.99  
% 3.87/0.99  --resolution_flag                       true
% 3.87/0.99  --res_lit_sel                           adaptive
% 3.87/0.99  --res_lit_sel_side                      none
% 3.87/0.99  --res_ordering                          kbo
% 3.87/0.99  --res_to_prop_solver                    active
% 3.87/0.99  --res_prop_simpl_new                    false
% 3.87/0.99  --res_prop_simpl_given                  true
% 3.87/0.99  --res_passive_queue_type                priority_queues
% 3.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.99  --res_passive_queues_freq               [15;5]
% 3.87/0.99  --res_forward_subs                      full
% 3.87/0.99  --res_backward_subs                     full
% 3.87/0.99  --res_forward_subs_resolution           true
% 3.87/0.99  --res_backward_subs_resolution          true
% 3.87/0.99  --res_orphan_elimination                true
% 3.87/0.99  --res_time_limit                        2.
% 3.87/0.99  --res_out_proof                         true
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Options
% 3.87/0.99  
% 3.87/0.99  --superposition_flag                    true
% 3.87/0.99  --sup_passive_queue_type                priority_queues
% 3.87/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.99  --sup_passive_queues_freq               [1;4]
% 3.87/0.99  --demod_completeness_check              fast
% 3.87/0.99  --demod_use_ground                      true
% 3.87/0.99  --sup_to_prop_solver                    passive
% 3.87/0.99  --sup_prop_simpl_new                    true
% 3.87/0.99  --sup_prop_simpl_given                  true
% 3.87/0.99  --sup_fun_splitting                     false
% 3.87/0.99  --sup_smt_interval                      50000
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Simplification Setup
% 3.87/0.99  
% 3.87/0.99  --sup_indices_passive                   []
% 3.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_full_bw                           [BwDemod]
% 3.87/0.99  --sup_immed_triv                        [TrivRules]
% 3.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_immed_bw_main                     []
% 3.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/0.99  
% 3.87/0.99  ------ Combination Options
% 3.87/0.99  
% 3.87/0.99  --comb_res_mult                         3
% 3.87/0.99  --comb_sup_mult                         2
% 3.87/0.99  --comb_inst_mult                        10
% 3.87/0.99  
% 3.87/0.99  ------ Debug Options
% 3.87/0.99  
% 3.87/0.99  --dbg_backtrace                         false
% 3.87/0.99  --dbg_dump_prop_clauses                 false
% 3.87/0.99  --dbg_dump_prop_clauses_file            -
% 3.87/0.99  --dbg_out_stat                          false
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ Proving...
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS status Theorem for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  fof(f20,conjecture,(
% 3.87/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f21,negated_conjecture,(
% 3.87/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.87/0.99    inference(negated_conjecture,[],[f20])).
% 3.87/0.99  
% 3.87/0.99  fof(f29,plain,(
% 3.87/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f21])).
% 3.87/0.99  
% 3.87/0.99  fof(f42,plain,(
% 3.87/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f43,plain,(
% 3.87/0.99    (k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)) & v1_relat_1(sK2)),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f42])).
% 3.87/0.99  
% 3.87/0.99  fof(f71,plain,(
% 3.87/0.99    v1_relat_1(sK2)),
% 3.87/0.99    inference(cnf_transformation,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f3,axiom,(
% 3.87/0.99    v1_xboole_0(k1_xboole_0)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f49,plain,(
% 3.87/0.99    v1_xboole_0(k1_xboole_0)),
% 3.87/0.99    inference(cnf_transformation,[],[f3])).
% 3.87/0.99  
% 3.87/0.99  fof(f14,axiom,(
% 3.87/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f23,plain,(
% 3.87/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f14])).
% 3.87/0.99  
% 3.87/0.99  fof(f64,plain,(
% 3.87/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f23])).
% 3.87/0.99  
% 3.87/0.99  fof(f15,axiom,(
% 3.87/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f24,plain,(
% 3.87/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f15])).
% 3.87/0.99  
% 3.87/0.99  fof(f25,plain,(
% 3.87/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.87/0.99    inference(flattening,[],[f24])).
% 3.87/0.99  
% 3.87/0.99  fof(f65,plain,(
% 3.87/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f25])).
% 3.87/0.99  
% 3.87/0.99  fof(f16,axiom,(
% 3.87/0.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f26,plain,(
% 3.87/0.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f16])).
% 3.87/0.99  
% 3.87/0.99  fof(f66,plain,(
% 3.87/0.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f26])).
% 3.87/0.99  
% 3.87/0.99  fof(f13,axiom,(
% 3.87/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f63,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.87/0.99    inference(cnf_transformation,[],[f13])).
% 3.87/0.99  
% 3.87/0.99  fof(f6,axiom,(
% 3.87/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f54,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f6])).
% 3.87/0.99  
% 3.87/0.99  fof(f7,axiom,(
% 3.87/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f55,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f7])).
% 3.87/0.99  
% 3.87/0.99  fof(f8,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f56,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f8])).
% 3.87/0.99  
% 3.87/0.99  fof(f9,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f57,plain,(
% 3.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f9])).
% 3.87/0.99  
% 3.87/0.99  fof(f10,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f58,plain,(
% 3.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f10])).
% 3.87/0.99  
% 3.87/0.99  fof(f11,axiom,(
% 3.87/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f59,plain,(
% 3.87/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f11])).
% 3.87/0.99  
% 3.87/0.99  fof(f73,plain,(
% 3.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.87/0.99  
% 3.87/0.99  fof(f74,plain,(
% 3.87/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f57,f73])).
% 3.87/0.99  
% 3.87/0.99  fof(f75,plain,(
% 3.87/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f56,f74])).
% 3.87/0.99  
% 3.87/0.99  fof(f76,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f55,f75])).
% 3.87/0.99  
% 3.87/0.99  fof(f77,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f54,f76])).
% 3.87/0.99  
% 3.87/0.99  fof(f78,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.87/0.99    inference(definition_unfolding,[],[f63,f77])).
% 3.87/0.99  
% 3.87/0.99  fof(f80,plain,(
% 3.87/0.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f66,f78])).
% 3.87/0.99  
% 3.87/0.99  fof(f19,axiom,(
% 3.87/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f70,plain,(
% 3.87/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.87/0.99    inference(cnf_transformation,[],[f19])).
% 3.87/0.99  
% 3.87/0.99  fof(f18,axiom,(
% 3.87/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f28,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f18])).
% 3.87/0.99  
% 3.87/0.99  fof(f68,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f28])).
% 3.87/0.99  
% 3.87/0.99  fof(f4,axiom,(
% 3.87/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f38,plain,(
% 3.87/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.99    inference(nnf_transformation,[],[f4])).
% 3.87/0.99  
% 3.87/0.99  fof(f39,plain,(
% 3.87/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.99    inference(flattening,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f52,plain,(
% 3.87/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f39])).
% 3.87/0.99  
% 3.87/0.99  fof(f2,axiom,(
% 3.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f22,plain,(
% 3.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f2])).
% 3.87/0.99  
% 3.87/0.99  fof(f34,plain,(
% 3.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.87/0.99    inference(nnf_transformation,[],[f22])).
% 3.87/0.99  
% 3.87/0.99  fof(f35,plain,(
% 3.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.87/0.99    inference(rectify,[],[f34])).
% 3.87/0.99  
% 3.87/0.99  fof(f36,plain,(
% 3.87/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f37,plain,(
% 3.87/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.87/0.99  
% 3.87/0.99  fof(f47,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f37])).
% 3.87/0.99  
% 3.87/0.99  fof(f1,axiom,(
% 3.87/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f30,plain,(
% 3.87/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.87/0.99    inference(nnf_transformation,[],[f1])).
% 3.87/0.99  
% 3.87/0.99  fof(f31,plain,(
% 3.87/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.87/0.99    inference(rectify,[],[f30])).
% 3.87/0.99  
% 3.87/0.99  fof(f32,plain,(
% 3.87/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f33,plain,(
% 3.87/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.87/0.99  
% 3.87/0.99  fof(f44,plain,(
% 3.87/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f33])).
% 3.87/0.99  
% 3.87/0.99  fof(f5,axiom,(
% 3.87/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f53,plain,(
% 3.87/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f5])).
% 3.87/0.99  
% 3.87/0.99  fof(f79,plain,(
% 3.87/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.87/0.99    inference(definition_unfolding,[],[f53,f78])).
% 3.87/0.99  
% 3.87/0.99  fof(f12,axiom,(
% 3.87/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f40,plain,(
% 3.87/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.87/0.99    inference(nnf_transformation,[],[f12])).
% 3.87/0.99  
% 3.87/0.99  fof(f41,plain,(
% 3.87/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.87/0.99    inference(flattening,[],[f40])).
% 3.87/0.99  
% 3.87/0.99  fof(f62,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.87/0.99    inference(cnf_transformation,[],[f41])).
% 3.87/0.99  
% 3.87/0.99  fof(f83,plain,(
% 3.87/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.87/0.99    inference(equality_resolution,[],[f62])).
% 3.87/0.99  
% 3.87/0.99  fof(f69,plain,(
% 3.87/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.87/0.99    inference(cnf_transformation,[],[f19])).
% 3.87/0.99  
% 3.87/0.99  fof(f17,axiom,(
% 3.87/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f27,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f17])).
% 3.87/0.99  
% 3.87/0.99  fof(f67,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f27])).
% 3.87/0.99  
% 3.87/0.99  fof(f61,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.87/0.99    inference(cnf_transformation,[],[f41])).
% 3.87/0.99  
% 3.87/0.99  fof(f84,plain,(
% 3.87/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.87/0.99    inference(equality_resolution,[],[f61])).
% 3.87/0.99  
% 3.87/0.99  fof(f46,plain,(
% 3.87/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f37])).
% 3.87/0.99  
% 3.87/0.99  fof(f72,plain,(
% 3.87/0.99    k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2)),
% 3.87/0.99    inference(cnf_transformation,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f50,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.87/0.99    inference(cnf_transformation,[],[f39])).
% 3.87/0.99  
% 3.87/0.99  fof(f82,plain,(
% 3.87/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.87/0.99    inference(equality_resolution,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f60,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f41])).
% 3.87/0.99  
% 3.87/0.99  cnf(c_21,negated_conjecture,
% 3.87/0.99      ( v1_relat_1(sK2) ),
% 3.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_489,plain,
% 3.87/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5,plain,
% 3.87/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_497,plain,
% 3.87/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_13,plain,
% 3.87/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_494,plain,
% 3.87/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_957,plain,
% 3.87/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_497,c_494]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_14,plain,
% 3.87/0.99      ( ~ v1_relat_1(X0)
% 3.87/0.99      | ~ v1_relat_1(X1)
% 3.87/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_493,plain,
% 3.87/0.99      ( v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_relat_1(X1) != iProver_top
% 3.87/0.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_15,plain,
% 3.87/0.99      ( ~ v1_relat_1(X0)
% 3.87/0.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_492,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1257,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 3.87/0.99      | v1_relat_1(X1) != iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_493,c_492]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2668,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_957,c_1257]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12800,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k2_relat_1(k5_relat_1(sK2,k1_xboole_0))))) = k5_relat_1(sK2,k1_xboole_0) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_489,c_2668]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_18,plain,
% 3.87/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_17,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.87/0.99      | ~ v1_relat_1(X1)
% 3.87/0.99      | ~ v1_relat_1(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_490,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.87/0.99      | v1_relat_1(X1) != iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_661,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_18,c_490]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_35,plain,
% 3.87/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_37,plain,
% 3.87/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_48,plain,
% 3.87/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1371,plain,
% 3.87/0.99      ( v1_relat_1(X0) != iProver_top
% 3.87/0.99      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_661,c_37,c_48]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1372,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_1371]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_496,plain,
% 3.87/0.99      ( X0 = X1
% 3.87/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.87/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1378,plain,
% 3.87/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X0,k1_xboole_0))) != iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1372,c_496]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_499,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.87/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1,plain,
% 3.87/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_501,plain,
% 3.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1137,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_499,c_501]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1592,plain,
% 3.87/0.99      ( X0 = X1
% 3.87/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1137,c_496]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1704,plain,
% 3.87/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/0.99      | v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1372,c_1592]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2009,plain,
% 3.87/0.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_1378,c_48,c_1704]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2017,plain,
% 3.87/0.99      ( k2_relat_1(k5_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_489,c_2009]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12824,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k5_relat_1(sK2,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK2,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK2,k1_xboole_0) ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_12800,c_2017]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10,plain,
% 3.87/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12825,plain,
% 3.87/0.99      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_12824,c_9,c_10]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2667,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k5_relat_1(X0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK2)),k2_relat_1(k5_relat_1(X0,sK2))))) = k5_relat_1(X0,sK2)
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_489,c_1257]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12085,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK2)),k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_957,c_2667]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_19,plain,
% 3.87/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_16,plain,
% 3.87/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.87/0.99      | ~ v1_relat_1(X1)
% 3.87/0.99      | ~ v1_relat_1(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_491,plain,
% 3.87/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.87/0.99      | v1_relat_1(X1) != iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_900,plain,
% 3.87/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_19,c_491]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1463,plain,
% 3.87/0.99      ( v1_relat_1(X0) != iProver_top
% 3.87/0.99      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_900,c_37,c_48]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1464,plain,
% 3.87/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_1463]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1470,plain,
% 3.87/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,X0))) != iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1464,c_496]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1705,plain,
% 3.87/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/0.99      | v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1464,c_1592]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2498,plain,
% 3.87/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_1470,c_48,c_1705]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2506,plain,
% 3.87/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_489,c_2498]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12104,plain,
% 3.87/0.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k5_relat_1(k1_xboole_0,sK2),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK2))))) = k5_relat_1(k1_xboole_0,sK2) ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_12085,c_2506]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11,plain,
% 3.87/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12105,plain,
% 3.87/0.99      ( k5_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_12104,c_9,c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_227,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.87/0.99      theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_223,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3538,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_227,c_223]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6666,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 3.87/0.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_3538,c_18]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_498,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.87/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.87/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1377,plain,
% 3.87/0.99      ( r2_hidden(X0,k2_relat_1(k5_relat_1(X1,k1_xboole_0))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1372,c_498]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1758,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
% 3.87/0.99      | r2_hidden(sK1(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1),k1_xboole_0) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_499,c_1377]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5506,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1758,c_501]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5640,plain,
% 3.87/0.99      ( v1_relat_1(X0) != iProver_top
% 3.87/0.99      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_5506,c_48]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5641,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),X1) = iProver_top
% 3.87/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_5640]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5646,plain,
% 3.87/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 3.87/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_2017,c_5641]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5688,plain,
% 3.87/0.99      ( r1_tarski(k1_xboole_0,X0) | ~ v1_relat_1(sK2) ),
% 3.87/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5646]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7338,plain,
% 3.87/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_6666,c_21,c_5688]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2578,plain,
% 3.87/0.99      ( X0 != k1_xboole_0 | k2_relat_1(k1_xboole_0) = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_224,c_18]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2580,plain,
% 3.87/0.99      ( X0 != X1 | X1 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_224,c_223]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3764,plain,
% 3.87/0.99      ( X0 = k2_relat_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2578,c_2580]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6703,plain,
% 3.87/0.99      ( r1_tarski(X0,X1)
% 3.87/0.99      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
% 3.87/0.99      | X0 != k1_xboole_0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_3538,c_3764]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7351,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) | X0 != k1_xboole_0 ),
% 3.87/0.99      inference(backward_subsumption_resolution,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7338,c_6703]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8002,plain,
% 3.87/0.99      ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),X1) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_7351,c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2996,plain,
% 3.87/0.99      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2580,c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3150,plain,
% 3.87/0.99      ( X0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2996,c_224]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4463,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,X1))
% 3.87/0.99      | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X0)
% 3.87/0.99      | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_3150,c_6]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8657,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_xboole_0,X1)) | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(backward_subsumption_resolution,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8002,c_4463]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_912,plain,
% 3.87/0.99      ( r1_tarski(X0,X1) | ~ v1_xboole_0(X0) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11080,plain,
% 3.87/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_8657,c_912]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8010,plain,
% 3.87/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_7351,c_223]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_20,negated_conjecture,
% 3.87/0.99      ( k1_xboole_0 != k5_relat_1(sK2,k1_xboole_0)
% 3.87/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
% 3.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1518,plain,
% 3.87/0.99      ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
% 3.87/0.99      | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK2,k1_xboole_0))
% 3.87/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_6,c_20]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8021,plain,
% 3.87/0.99      ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
% 3.87/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK2) ),
% 3.87/0.99      inference(backward_subsumption_resolution,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8010,c_1518]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11096,plain,
% 3.87/0.99      ( ~ r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
% 3.87/0.99      | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK2)) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_11080,c_8021]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_225,plain,
% 3.87/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.87/0.99      theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1663,plain,
% 3.87/0.99      ( ~ v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK2))
% 3.87/0.99      | k5_relat_1(k1_xboole_0,sK2) != X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_225]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1665,plain,
% 3.87/0.99      ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK2))
% 3.87/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.87/0.99      | k5_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1663]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1129,plain,
% 3.87/0.99      ( ~ r1_tarski(X0,X1)
% 3.87/0.99      | r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
% 3.87/0.99      | k5_relat_1(sK2,k1_xboole_0) != X0
% 3.87/0.99      | k1_xboole_0 != X1 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_227]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1131,plain,
% 3.87/0.99      ( r1_tarski(k5_relat_1(sK2,k1_xboole_0),k1_xboole_0)
% 3.87/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.87/0.99      | k5_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 3.87/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1129]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8,plain,
% 3.87/0.99      ( r1_tarski(X0,X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_42,plain,
% 3.87/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_39,plain,
% 3.87/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12,plain,
% 3.87/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.87/0.99      | k1_xboole_0 = X1
% 3.87/0.99      | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_38,plain,
% 3.87/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.87/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(contradiction,plain,
% 3.87/0.99      ( $false ),
% 3.87/0.99      inference(minisat,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_12825,c_12105,c_11096,c_1665,c_1131,c_5,c_42,c_39,
% 3.87/0.99                 c_38]) ).
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  ------                               Statistics
% 3.87/0.99  
% 3.87/0.99  ------ Selected
% 3.87/0.99  
% 3.87/0.99  total_time:                             0.419
% 3.87/0.99  
%------------------------------------------------------------------------------
