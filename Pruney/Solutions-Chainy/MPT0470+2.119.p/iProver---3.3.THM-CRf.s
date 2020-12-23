%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:16 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  169 (1073 expanded)
%              Number of clauses        :   73 ( 134 expanded)
%              Number of leaves         :   31 ( 324 expanded)
%              Depth                    :   21
%              Number of atoms          :  351 (1497 expanded)
%              Number of equality atoms :  222 (1176 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f92])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f48,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f48,f47])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f27,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f42,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f50,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f50])).

fof(f83,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f89])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f98,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f71,f91,f92,f92,f92])).

fof(f100,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f90])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f90])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f72,f91,f92,f92,f92])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_263,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | v1_relat_1(X2)
    | X2 != X1
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_14])).

cnf(c_264,plain,
    ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0)
    | v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_897,plain,
    ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_907,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1165,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_907])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_899,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_908,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_901,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1846,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_901])).

cnf(c_21,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1848,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1846,c_21])).

cnf(c_1944,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_1848])).

cnf(c_3591,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_1944])).

cnf(c_3782,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1165,c_3591])).

cnf(c_12,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_911,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12,c_1,c_6])).

cnf(c_21025,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3782,c_911])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_903,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_902,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1417,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_902])).

cnf(c_3519,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_1417])).

cnf(c_14771,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_899,c_3519])).

cnf(c_21226,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(demodulation,[status(thm)],[c_21025,c_14771])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_910,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_905,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_909,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1175,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_909])).

cnf(c_1180,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_910,c_1175])).

cnf(c_21227,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21226,c_3,c_1180])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_47,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_639,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_935,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_936,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_984,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_985,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_3518,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_1417])).

cnf(c_3874,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1165,c_3518])).

cnf(c_19,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_900,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1510,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_900])).

cnf(c_1512,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1510,c_20])).

cnf(c_1938,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_1512])).

cnf(c_3029,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_1938])).

cnf(c_3036,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1165,c_3029])).

cnf(c_3149,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3036,c_911])).

cnf(c_3875,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3874,c_3149])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_906,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1254,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_909])).

cnf(c_1326,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_910,c_1254])).

cnf(c_3876,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3875,c_3,c_1326])).

cnf(c_4400,plain,
    ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3876,c_911])).

cnf(c_21238,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21227,c_22,c_46,c_47,c_936,c_985,c_4400])).

cnf(c_21240,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_21238,c_911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.53/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/2.00  
% 11.53/2.00  ------  iProver source info
% 11.53/2.00  
% 11.53/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.53/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/2.00  git: non_committed_changes: false
% 11.53/2.00  git: last_make_outside_of_git: false
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     num_symb
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       true
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  ------ Parsing...
% 11.53/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/2.00  ------ Proving...
% 11.53/2.00  ------ Problem Properties 
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  clauses                                 22
% 11.53/2.00  conjectures                             2
% 11.53/2.00  EPR                                     5
% 11.53/2.00  Horn                                    20
% 11.53/2.00  unary                                   9
% 11.53/2.00  binary                                  9
% 11.53/2.00  lits                                    41
% 11.53/2.00  lits eq                                 17
% 11.53/2.00  fd_pure                                 0
% 11.53/2.00  fd_pseudo                               0
% 11.53/2.00  fd_cond                                 2
% 11.53/2.00  fd_pseudo_cond                          1
% 11.53/2.00  AC symbols                              0
% 11.53/2.00  
% 11.53/2.00  ------ Schedule dynamic 5 is on 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  Current options:
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     none
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       false
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ Proving...
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  % SZS status Theorem for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00   Resolution empty clause
% 11.53/2.00  
% 11.53/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  fof(f18,axiom,(
% 11.53/2.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f43,plain,(
% 11.53/2.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.53/2.00    inference(nnf_transformation,[],[f18])).
% 11.53/2.00  
% 11.53/2.00  fof(f70,plain,(
% 11.53/2.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f43])).
% 11.53/2.00  
% 11.53/2.00  fof(f9,axiom,(
% 11.53/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f60,plain,(
% 11.53/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f9])).
% 11.53/2.00  
% 11.53/2.00  fof(f10,axiom,(
% 11.53/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f61,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f10])).
% 11.53/2.00  
% 11.53/2.00  fof(f11,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f62,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f11])).
% 11.53/2.00  
% 11.53/2.00  fof(f12,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f63,plain,(
% 11.53/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f12])).
% 11.53/2.00  
% 11.53/2.00  fof(f13,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f64,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f13])).
% 11.53/2.00  
% 11.53/2.00  fof(f14,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f65,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f14])).
% 11.53/2.00  
% 11.53/2.00  fof(f15,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f66,plain,(
% 11.53/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f15])).
% 11.53/2.00  
% 11.53/2.00  fof(f85,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f65,f66])).
% 11.53/2.00  
% 11.53/2.00  fof(f86,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f64,f85])).
% 11.53/2.00  
% 11.53/2.00  fof(f87,plain,(
% 11.53/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f63,f86])).
% 11.53/2.00  
% 11.53/2.00  fof(f88,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f62,f87])).
% 11.53/2.00  
% 11.53/2.00  fof(f89,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f61,f88])).
% 11.53/2.00  
% 11.53/2.00  fof(f92,plain,(
% 11.53/2.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f60,f89])).
% 11.53/2.00  
% 11.53/2.00  fof(f95,plain,(
% 11.53/2.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f70,f92])).
% 11.53/2.00  
% 11.53/2.00  fof(f21,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f34,plain,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 11.53/2.00    inference(ennf_transformation,[],[f21])).
% 11.53/2.00  
% 11.53/2.00  fof(f45,plain,(
% 11.53/2.00    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(nnf_transformation,[],[f34])).
% 11.53/2.00  
% 11.53/2.00  fof(f46,plain,(
% 11.53/2.00    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(rectify,[],[f45])).
% 11.53/2.00  
% 11.53/2.00  fof(f48,plain,(
% 11.53/2.00    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f47,plain,(
% 11.53/2.00    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f49,plain,(
% 11.53/2.00    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f48,f47])).
% 11.53/2.00  
% 11.53/2.00  fof(f75,plain,(
% 11.53/2.00    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f49])).
% 11.53/2.00  
% 11.53/2.00  fof(f7,axiom,(
% 11.53/2.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f31,plain,(
% 11.53/2.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.53/2.00    inference(ennf_transformation,[],[f7])).
% 11.53/2.00  
% 11.53/2.00  fof(f58,plain,(
% 11.53/2.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f31])).
% 11.53/2.00  
% 11.53/2.00  fof(f27,conjecture,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f28,negated_conjecture,(
% 11.53/2.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.53/2.00    inference(negated_conjecture,[],[f27])).
% 11.53/2.00  
% 11.53/2.00  fof(f42,plain,(
% 11.53/2.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f28])).
% 11.53/2.00  
% 11.53/2.00  fof(f50,plain,(
% 11.53/2.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f51,plain,(
% 11.53/2.00    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f50])).
% 11.53/2.00  
% 11.53/2.00  fof(f83,plain,(
% 11.53/2.00    v1_relat_1(sK3)),
% 11.53/2.00    inference(cnf_transformation,[],[f51])).
% 11.53/2.00  
% 11.53/2.00  fof(f6,axiom,(
% 11.53/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f57,plain,(
% 11.53/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f6])).
% 11.53/2.00  
% 11.53/2.00  fof(f26,axiom,(
% 11.53/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f82,plain,(
% 11.53/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.53/2.00    inference(cnf_transformation,[],[f26])).
% 11.53/2.00  
% 11.53/2.00  fof(f24,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f38,plain,(
% 11.53/2.00    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f24])).
% 11.53/2.00  
% 11.53/2.00  fof(f39,plain,(
% 11.53/2.00    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(flattening,[],[f38])).
% 11.53/2.00  
% 11.53/2.00  fof(f79,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f39])).
% 11.53/2.00  
% 11.53/2.00  fof(f81,plain,(
% 11.53/2.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.53/2.00    inference(cnf_transformation,[],[f26])).
% 11.53/2.00  
% 11.53/2.00  fof(f19,axiom,(
% 11.53/2.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f44,plain,(
% 11.53/2.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.53/2.00    inference(nnf_transformation,[],[f19])).
% 11.53/2.00  
% 11.53/2.00  fof(f71,plain,(
% 11.53/2.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f44])).
% 11.53/2.00  
% 11.53/2.00  fof(f4,axiom,(
% 11.53/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f55,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f4])).
% 11.53/2.00  
% 11.53/2.00  fof(f20,axiom,(
% 11.53/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f73,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f20])).
% 11.53/2.00  
% 11.53/2.00  fof(f90,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.53/2.00    inference(definition_unfolding,[],[f73,f89])).
% 11.53/2.00  
% 11.53/2.00  fof(f91,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.53/2.00    inference(definition_unfolding,[],[f55,f90])).
% 11.53/2.00  
% 11.53/2.00  fof(f98,plain,(
% 11.53/2.00    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f71,f91,f92,f92,f92])).
% 11.53/2.00  
% 11.53/2.00  fof(f100,plain,(
% 11.53/2.00    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.53/2.00    inference(equality_resolution,[],[f98])).
% 11.53/2.00  
% 11.53/2.00  fof(f2,axiom,(
% 11.53/2.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f29,plain,(
% 11.53/2.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.53/2.00    inference(rectify,[],[f2])).
% 11.53/2.00  
% 11.53/2.00  fof(f53,plain,(
% 11.53/2.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.53/2.00    inference(cnf_transformation,[],[f29])).
% 11.53/2.00  
% 11.53/2.00  fof(f93,plain,(
% 11.53/2.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 11.53/2.00    inference(definition_unfolding,[],[f53,f90])).
% 11.53/2.00  
% 11.53/2.00  fof(f8,axiom,(
% 11.53/2.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f59,plain,(
% 11.53/2.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f8])).
% 11.53/2.00  
% 11.53/2.00  fof(f22,axiom,(
% 11.53/2.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f35,plain,(
% 11.53/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.53/2.00    inference(ennf_transformation,[],[f22])).
% 11.53/2.00  
% 11.53/2.00  fof(f36,plain,(
% 11.53/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(flattening,[],[f35])).
% 11.53/2.00  
% 11.53/2.00  fof(f77,plain,(
% 11.53/2.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f36])).
% 11.53/2.00  
% 11.53/2.00  fof(f23,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f37,plain,(
% 11.53/2.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f23])).
% 11.53/2.00  
% 11.53/2.00  fof(f78,plain,(
% 11.53/2.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f37])).
% 11.53/2.00  
% 11.53/2.00  fof(f99,plain,(
% 11.53/2.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(definition_unfolding,[],[f78,f90])).
% 11.53/2.00  
% 11.53/2.00  fof(f5,axiom,(
% 11.53/2.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f56,plain,(
% 11.53/2.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f5])).
% 11.53/2.00  
% 11.53/2.00  fof(f94,plain,(
% 11.53/2.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 11.53/2.00    inference(definition_unfolding,[],[f56,f90])).
% 11.53/2.00  
% 11.53/2.00  fof(f1,axiom,(
% 11.53/2.00    v1_xboole_0(k1_xboole_0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f52,plain,(
% 11.53/2.00    v1_xboole_0(k1_xboole_0)),
% 11.53/2.00    inference(cnf_transformation,[],[f1])).
% 11.53/2.00  
% 11.53/2.00  fof(f17,axiom,(
% 11.53/2.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f33,plain,(
% 11.53/2.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f17])).
% 11.53/2.00  
% 11.53/2.00  fof(f68,plain,(
% 11.53/2.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f33])).
% 11.53/2.00  
% 11.53/2.00  fof(f3,axiom,(
% 11.53/2.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f30,plain,(
% 11.53/2.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f3])).
% 11.53/2.00  
% 11.53/2.00  fof(f54,plain,(
% 11.53/2.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f30])).
% 11.53/2.00  
% 11.53/2.00  fof(f84,plain,(
% 11.53/2.00    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 11.53/2.00    inference(cnf_transformation,[],[f51])).
% 11.53/2.00  
% 11.53/2.00  fof(f72,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 11.53/2.00    inference(cnf_transformation,[],[f44])).
% 11.53/2.00  
% 11.53/2.00  fof(f97,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 11.53/2.00    inference(definition_unfolding,[],[f72,f91,f92,f92,f92])).
% 11.53/2.00  
% 11.53/2.00  fof(f25,axiom,(
% 11.53/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f40,plain,(
% 11.53/2.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f25])).
% 11.53/2.00  
% 11.53/2.00  fof(f41,plain,(
% 11.53/2.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.53/2.00    inference(flattening,[],[f40])).
% 11.53/2.00  
% 11.53/2.00  fof(f80,plain,(
% 11.53/2.00    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f41])).
% 11.53/2.00  
% 11.53/2.00  fof(f16,axiom,(
% 11.53/2.00    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f32,plain,(
% 11.53/2.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 11.53/2.00    inference(ennf_transformation,[],[f16])).
% 11.53/2.00  
% 11.53/2.00  fof(f67,plain,(
% 11.53/2.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f32])).
% 11.53/2.00  
% 11.53/2.00  cnf(c_9,plain,
% 11.53/2.00      ( ~ r2_hidden(X0,X1)
% 11.53/2.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.53/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_145,plain,
% 11.53/2.00      ( ~ r2_hidden(X0,X1)
% 11.53/2.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.53/2.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_14,plain,
% 11.53/2.00      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_263,plain,
% 11.53/2.00      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 11.53/2.00      | v1_relat_1(X2)
% 11.53/2.00      | X2 != X1
% 11.53/2.00      | sK0(X2) != X0 ),
% 11.53/2.00      inference(resolution_lifted,[status(thm)],[c_145,c_14]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_264,plain,
% 11.53/2.00      ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0)
% 11.53/2.00      | v1_relat_1(X0) ),
% 11.53/2.00      inference(unflattening,[status(thm)],[c_263]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_897,plain,
% 11.53/2.00      ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = iProver_top
% 11.53/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_5,plain,
% 11.53/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_907,plain,
% 11.53/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1165,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_897,c_907]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_23,negated_conjecture,
% 11.53/2.00      ( v1_relat_1(sK3) ),
% 11.53/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_899,plain,
% 11.53/2.00      ( v1_relat_1(sK3) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4,plain,
% 11.53/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_908,plain,
% 11.53/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_20,plain,
% 11.53/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_18,plain,
% 11.53/2.00      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 11.53/2.00      | ~ v1_relat_1(X0)
% 11.53/2.00      | ~ v1_relat_1(X1)
% 11.53/2.00      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_901,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 11.53/2.00      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1846,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 11.53/2.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_20,c_901]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21,plain,
% 11.53/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1848,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 11.53/2.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(light_normalisation,[status(thm)],[c_1846,c_21]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1944,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_908,c_1848]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3591,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_899,c_1944]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3782,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_1165,c_3591]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_12,plain,
% 11.53/2.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1,plain,
% 11.53/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_6,plain,
% 11.53/2.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_911,plain,
% 11.53/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.53/2.00      inference(demodulation,[status(thm)],[c_12,c_1,c_6]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21025,plain,
% 11.53/2.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_3782,c_911]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_16,plain,
% 11.53/2.00      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_903,plain,
% 11.53/2.00      ( v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(X1) != iProver_top
% 11.53/2.00      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_17,plain,
% 11.53/2.00      ( ~ v1_relat_1(X0)
% 11.53/2.00      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_902,plain,
% 11.53/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 11.53/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1417,plain,
% 11.53/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_903,c_902]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3519,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 11.53/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_1165,c_1417]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_14771,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_899,c_3519]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21226,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 11.53/2.00      inference(demodulation,[status(thm)],[c_21025,c_14771]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3,plain,
% 11.53/2.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_0,plain,
% 11.53/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_910,plain,
% 11.53/2.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_8,plain,
% 11.53/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_905,plain,
% 11.53/2.00      ( v1_xboole_0(X0) != iProver_top
% 11.53/2.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_2,plain,
% 11.53/2.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_909,plain,
% 11.53/2.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1175,plain,
% 11.53/2.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_905,c_909]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1180,plain,
% 11.53/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_910,c_1175]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21227,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 11.53/2.00      inference(demodulation,[status(thm)],[c_21226,c_3,c_1180]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_22,negated_conjecture,
% 11.53/2.00      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 11.53/2.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 11.53/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_46,plain,
% 11.53/2.00      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_11,plain,
% 11.53/2.00      ( X0 = X1
% 11.53/2.00      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 11.53/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_47,plain,
% 11.53/2.00      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 11.53/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_935,plain,
% 11.53/2.00      ( k5_relat_1(sK3,k1_xboole_0) != X0
% 11.53/2.00      | k1_xboole_0 != X0
% 11.53/2.00      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_639]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_936,plain,
% 11.53/2.00      ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 11.53/2.00      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
% 11.53/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_935]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_984,plain,
% 11.53/2.00      ( k5_relat_1(k1_xboole_0,sK3) != X0
% 11.53/2.00      | k1_xboole_0 != X0
% 11.53/2.00      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_639]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_985,plain,
% 11.53/2.00      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 11.53/2.00      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
% 11.53/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.53/2.00      inference(instantiation,[status(thm)],[c_984]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3518,plain,
% 11.53/2.00      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 11.53/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_899,c_1417]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3874,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_1165,c_3518]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_19,plain,
% 11.53/2.00      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 11.53/2.00      | ~ v1_relat_1(X0)
% 11.53/2.00      | ~ v1_relat_1(X1)
% 11.53/2.00      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_900,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 11.53/2.00      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 11.53/2.00      | v1_relat_1(X1) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1510,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 11.53/2.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_21,c_900]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1512,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(light_normalisation,[status(thm)],[c_1510,c_20]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1938,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | v1_relat_1(X0) != iProver_top
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_908,c_1512]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3029,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_899,c_1938]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3036,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_1165,c_3029]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3149,plain,
% 11.53/2.00      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_3036,c_911]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3875,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 11.53/2.00      inference(light_normalisation,[status(thm)],[c_3874,c_3149]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_7,plain,
% 11.53/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_906,plain,
% 11.53/2.00      ( v1_xboole_0(X0) != iProver_top
% 11.53/2.00      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1254,plain,
% 11.53/2.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_906,c_909]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1326,plain,
% 11.53/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_910,c_1254]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_3876,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.53/2.00      | k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.00      inference(demodulation,[status(thm)],[c_3875,c_3,c_1326]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4400,plain,
% 11.53/2.00      ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_3876,c_911]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21238,plain,
% 11.53/2.00      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0 ),
% 11.53/2.00      inference(global_propositional_subsumption,
% 11.53/2.00                [status(thm)],
% 11.53/2.00                [c_21227,c_22,c_46,c_47,c_936,c_985,c_4400]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_21240,plain,
% 11.53/2.00      ( $false ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_21238,c_911]) ).
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  ------                               Statistics
% 11.53/2.00  
% 11.53/2.00  ------ General
% 11.53/2.00  
% 11.53/2.00  abstr_ref_over_cycles:                  0
% 11.53/2.00  abstr_ref_under_cycles:                 0
% 11.53/2.00  gc_basic_clause_elim:                   0
% 11.53/2.00  forced_gc_time:                         0
% 11.53/2.00  parsing_time:                           0.007
% 11.53/2.00  unif_index_cands_time:                  0.
% 11.53/2.00  unif_index_add_time:                    0.
% 11.53/2.00  orderings_time:                         0.
% 11.53/2.00  out_proof_time:                         0.01
% 11.53/2.00  total_time:                             1.176
% 11.53/2.00  num_of_symbols:                         48
% 11.53/2.00  num_of_terms:                           12407
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing
% 11.53/2.00  
% 11.53/2.00  num_of_splits:                          0
% 11.53/2.00  num_of_split_atoms:                     0
% 11.53/2.00  num_of_reused_defs:                     0
% 11.53/2.00  num_eq_ax_congr_red:                    10
% 11.53/2.00  num_of_sem_filtered_clauses:            1
% 11.53/2.00  num_of_subtypes:                        0
% 11.53/2.00  monotx_restored_types:                  0
% 11.53/2.00  sat_num_of_epr_types:                   0
% 11.53/2.00  sat_num_of_non_cyclic_types:            0
% 11.53/2.00  sat_guarded_non_collapsed_types:        0
% 11.53/2.00  num_pure_diseq_elim:                    0
% 11.53/2.00  simp_replaced_by:                       0
% 11.53/2.00  res_preprocessed:                       117
% 11.53/2.00  prep_upred:                             0
% 11.53/2.00  prep_unflattend:                        24
% 11.53/2.00  smt_new_axioms:                         0
% 11.53/2.00  pred_elim_cands:                        3
% 11.53/2.00  pred_elim:                              1
% 11.53/2.00  pred_elim_cl:                           2
% 11.53/2.00  pred_elim_cycles:                       3
% 11.53/2.00  merged_defs:                            2
% 11.53/2.00  merged_defs_ncl:                        0
% 11.53/2.00  bin_hyper_res:                          2
% 11.53/2.00  prep_cycles:                            4
% 11.53/2.00  pred_elim_time:                         0.003
% 11.53/2.00  splitting_time:                         0.
% 11.53/2.00  sem_filter_time:                        0.
% 11.53/2.00  monotx_time:                            0.
% 11.53/2.00  subtype_inf_time:                       0.
% 11.53/2.00  
% 11.53/2.00  ------ Problem properties
% 11.53/2.00  
% 11.53/2.00  clauses:                                22
% 11.53/2.00  conjectures:                            2
% 11.53/2.00  epr:                                    5
% 11.53/2.00  horn:                                   20
% 11.53/2.00  ground:                                 5
% 11.53/2.00  unary:                                  9
% 11.53/2.00  binary:                                 9
% 11.53/2.00  lits:                                   41
% 11.53/2.00  lits_eq:                                17
% 11.53/2.00  fd_pure:                                0
% 11.53/2.00  fd_pseudo:                              0
% 11.53/2.00  fd_cond:                                2
% 11.53/2.00  fd_pseudo_cond:                         1
% 11.53/2.00  ac_symbols:                             0
% 11.53/2.00  
% 11.53/2.00  ------ Propositional Solver
% 11.53/2.00  
% 11.53/2.00  prop_solver_calls:                      35
% 11.53/2.00  prop_fast_solver_calls:                 1266
% 11.53/2.00  smt_solver_calls:                       0
% 11.53/2.00  smt_fast_solver_calls:                  0
% 11.53/2.00  prop_num_of_clauses:                    5476
% 11.53/2.00  prop_preprocess_simplified:             10912
% 11.53/2.00  prop_fo_subsumed:                       7
% 11.53/2.00  prop_solver_time:                       0.
% 11.53/2.00  smt_solver_time:                        0.
% 11.53/2.00  smt_fast_solver_time:                   0.
% 11.53/2.00  prop_fast_solver_time:                  0.
% 11.53/2.00  prop_unsat_core_time:                   0.
% 11.53/2.00  
% 11.53/2.00  ------ QBF
% 11.53/2.00  
% 11.53/2.00  qbf_q_res:                              0
% 11.53/2.00  qbf_num_tautologies:                    0
% 11.53/2.00  qbf_prep_cycles:                        0
% 11.53/2.00  
% 11.53/2.00  ------ BMC1
% 11.53/2.00  
% 11.53/2.00  bmc1_current_bound:                     -1
% 11.53/2.00  bmc1_last_solved_bound:                 -1
% 11.53/2.00  bmc1_unsat_core_size:                   -1
% 11.53/2.00  bmc1_unsat_core_parents_size:           -1
% 11.53/2.00  bmc1_merge_next_fun:                    0
% 11.53/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation
% 11.53/2.00  
% 11.53/2.00  inst_num_of_clauses:                    2168
% 11.53/2.00  inst_num_in_passive:                    179
% 11.53/2.00  inst_num_in_active:                     1099
% 11.53/2.00  inst_num_in_unprocessed:                891
% 11.53/2.00  inst_num_of_loops:                      1500
% 11.53/2.00  inst_num_of_learning_restarts:          0
% 11.53/2.00  inst_num_moves_active_passive:          395
% 11.53/2.00  inst_lit_activity:                      0
% 11.53/2.00  inst_lit_activity_moves:                0
% 11.53/2.00  inst_num_tautologies:                   0
% 11.53/2.00  inst_num_prop_implied:                  0
% 11.53/2.00  inst_num_existing_simplified:           0
% 11.53/2.00  inst_num_eq_res_simplified:             0
% 11.53/2.00  inst_num_child_elim:                    0
% 11.53/2.00  inst_num_of_dismatching_blockings:      2856
% 11.53/2.00  inst_num_of_non_proper_insts:           5197
% 11.53/2.00  inst_num_of_duplicates:                 0
% 11.53/2.00  inst_inst_num_from_inst_to_res:         0
% 11.53/2.00  inst_dismatching_checking_time:         0.
% 11.53/2.00  
% 11.53/2.00  ------ Resolution
% 11.53/2.00  
% 11.53/2.00  res_num_of_clauses:                     0
% 11.53/2.00  res_num_in_passive:                     0
% 11.53/2.00  res_num_in_active:                      0
% 11.53/2.00  res_num_of_loops:                       121
% 11.53/2.00  res_forward_subset_subsumed:            234
% 11.53/2.00  res_backward_subset_subsumed:           6
% 11.53/2.00  res_forward_subsumed:                   0
% 11.53/2.00  res_backward_subsumed:                  0
% 11.53/2.00  res_forward_subsumption_resolution:     0
% 11.53/2.00  res_backward_subsumption_resolution:    0
% 11.53/2.00  res_clause_to_clause_subsumption:       20868
% 11.53/2.00  res_orphan_elimination:                 0
% 11.53/2.00  res_tautology_del:                      699
% 11.53/2.00  res_num_eq_res_simplified:              0
% 11.53/2.00  res_num_sel_changes:                    0
% 11.53/2.00  res_moves_from_active_to_pass:          0
% 11.53/2.00  
% 11.53/2.00  ------ Superposition
% 11.53/2.00  
% 11.53/2.00  sup_time_total:                         0.
% 11.53/2.00  sup_time_generating:                    0.
% 11.53/2.00  sup_time_sim_full:                      0.
% 11.53/2.00  sup_time_sim_immed:                     0.
% 11.53/2.00  
% 11.53/2.00  sup_num_of_clauses:                     441
% 11.53/2.00  sup_num_in_active:                      276
% 11.53/2.00  sup_num_in_passive:                     165
% 11.53/2.00  sup_num_of_loops:                       299
% 11.53/2.00  sup_fw_superposition:                   637
% 11.53/2.00  sup_bw_superposition:                   104
% 11.53/2.00  sup_immediate_simplified:               185
% 11.53/2.00  sup_given_eliminated:                   9
% 11.53/2.00  comparisons_done:                       0
% 11.53/2.00  comparisons_avoided:                    11
% 11.53/2.00  
% 11.53/2.00  ------ Simplifications
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  sim_fw_subset_subsumed:                 34
% 11.53/2.00  sim_bw_subset_subsumed:                 96
% 11.53/2.00  sim_fw_subsumed:                        7
% 11.53/2.00  sim_bw_subsumed:                        17
% 11.53/2.00  sim_fw_subsumption_res:                 0
% 11.53/2.00  sim_bw_subsumption_res:                 0
% 11.53/2.00  sim_tautology_del:                      3
% 11.53/2.00  sim_eq_tautology_del:                   55
% 11.53/2.00  sim_eq_res_simp:                        1
% 11.53/2.00  sim_fw_demodulated:                     114
% 11.53/2.00  sim_bw_demodulated:                     12
% 11.53/2.00  sim_light_normalised:                   74
% 11.53/2.00  sim_joinable_taut:                      0
% 11.53/2.00  sim_joinable_simp:                      0
% 11.53/2.00  sim_ac_normalised:                      0
% 11.53/2.00  sim_smt_subsumption:                    0
% 11.53/2.00  
%------------------------------------------------------------------------------
