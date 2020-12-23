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
% DateTime   : Thu Dec  3 11:44:17 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  155 (1053 expanded)
%              Number of clauses        :   63 ( 120 expanded)
%              Number of leaves         :   28 ( 320 expanded)
%              Depth                    :   21
%              Number of atoms          :  334 (1481 expanded)
%              Number of equality atoms :  228 (1190 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f83])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f84])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f46])).

fof(f78,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f94,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f93,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f66,f86,f87,f87,f87])).

fof(f97,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f79,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f67,f86,f87,f87,f87])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_119,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_224,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | v1_relat_1(X2)
    | X2 != X1
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_119,c_13])).

cnf(c_225,plain,
    ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0)
    | v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_758,plain,
    ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_766,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1011,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_766])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_760,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_764,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_763,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1121,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_764,c_763])).

cnf(c_2212,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_1121])).

cnf(c_2495,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_2212])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_767,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_761,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1195,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_761])).

cnf(c_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1197,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1195,c_19])).

cnf(c_1226,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_1197])).

cnf(c_1285,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_1226])).

cnf(c_1593,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1011,c_1285])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_768,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11,c_0,c_4])).

cnf(c_7246,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1593,c_768])).

cnf(c_26071,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2495,c_7246])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_26072,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26071,c_1,c_7])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_45,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_572,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_786,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_787,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_807,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_808,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_2213,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1121])).

cnf(c_19638,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_760,c_2213])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_762,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1205,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_762])).

cnf(c_1207,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1205,c_20])).

cnf(c_1232,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_1207])).

cnf(c_1365,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_1232])).

cnf(c_1592,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1011,c_1365])).

cnf(c_6392,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1592,c_768])).

cnf(c_19642,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_19638,c_6392])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_19643,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
    | k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19642,c_1,c_8])).

cnf(c_19697,plain,
    ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19643,c_768])).

cnf(c_26073,plain,
    ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26072,c_21,c_45,c_46,c_787,c_808,c_19697])).

cnf(c_26076,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_26073,c_768])).

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
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.73/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/1.99  
% 11.73/1.99  ------  iProver source info
% 11.73/1.99  
% 11.73/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.73/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/1.99  git: non_committed_changes: false
% 11.73/1.99  git: last_make_outside_of_git: false
% 11.73/1.99  
% 11.73/1.99  ------ 
% 11.73/1.99  
% 11.73/1.99  ------ Input Options
% 11.73/1.99  
% 11.73/1.99  --out_options                           all
% 11.73/1.99  --tptp_safe_out                         true
% 11.73/1.99  --problem_path                          ""
% 11.73/1.99  --include_path                          ""
% 11.73/1.99  --clausifier                            res/vclausify_rel
% 11.73/1.99  --clausifier_options                    ""
% 11.73/1.99  --stdin                                 false
% 11.73/1.99  --stats_out                             all
% 11.73/1.99  
% 11.73/1.99  ------ General Options
% 11.73/1.99  
% 11.73/1.99  --fof                                   false
% 11.73/1.99  --time_out_real                         305.
% 11.73/1.99  --time_out_virtual                      -1.
% 11.73/1.99  --symbol_type_check                     false
% 11.73/1.99  --clausify_out                          false
% 11.73/1.99  --sig_cnt_out                           false
% 11.73/1.99  --trig_cnt_out                          false
% 11.73/1.99  --trig_cnt_out_tolerance                1.
% 11.73/1.99  --trig_cnt_out_sk_spl                   false
% 11.73/1.99  --abstr_cl_out                          false
% 11.73/1.99  
% 11.73/1.99  ------ Global Options
% 11.73/1.99  
% 11.73/1.99  --schedule                              default
% 11.73/1.99  --add_important_lit                     false
% 11.73/1.99  --prop_solver_per_cl                    1000
% 11.73/1.99  --min_unsat_core                        false
% 11.73/1.99  --soft_assumptions                      false
% 11.73/1.99  --soft_lemma_size                       3
% 11.73/1.99  --prop_impl_unit_size                   0
% 11.73/1.99  --prop_impl_unit                        []
% 11.73/1.99  --share_sel_clauses                     true
% 11.73/1.99  --reset_solvers                         false
% 11.73/1.99  --bc_imp_inh                            [conj_cone]
% 11.73/1.99  --conj_cone_tolerance                   3.
% 11.73/1.99  --extra_neg_conj                        none
% 11.73/1.99  --large_theory_mode                     true
% 11.73/1.99  --prolific_symb_bound                   200
% 11.73/1.99  --lt_threshold                          2000
% 11.73/1.99  --clause_weak_htbl                      true
% 11.73/1.99  --gc_record_bc_elim                     false
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing Options
% 11.73/1.99  
% 11.73/1.99  --preprocessing_flag                    true
% 11.73/1.99  --time_out_prep_mult                    0.1
% 11.73/1.99  --splitting_mode                        input
% 11.73/1.99  --splitting_grd                         true
% 11.73/1.99  --splitting_cvd                         false
% 11.73/1.99  --splitting_cvd_svl                     false
% 11.73/1.99  --splitting_nvd                         32
% 11.73/1.99  --sub_typing                            true
% 11.73/1.99  --prep_gs_sim                           true
% 11.73/1.99  --prep_unflatten                        true
% 11.73/1.99  --prep_res_sim                          true
% 11.73/1.99  --prep_upred                            true
% 11.73/1.99  --prep_sem_filter                       exhaustive
% 11.73/1.99  --prep_sem_filter_out                   false
% 11.73/1.99  --pred_elim                             true
% 11.73/1.99  --res_sim_input                         true
% 11.73/1.99  --eq_ax_congr_red                       true
% 11.73/1.99  --pure_diseq_elim                       true
% 11.73/1.99  --brand_transform                       false
% 11.73/1.99  --non_eq_to_eq                          false
% 11.73/1.99  --prep_def_merge                        true
% 11.73/1.99  --prep_def_merge_prop_impl              false
% 11.73/1.99  --prep_def_merge_mbd                    true
% 11.73/1.99  --prep_def_merge_tr_red                 false
% 11.73/1.99  --prep_def_merge_tr_cl                  false
% 11.73/1.99  --smt_preprocessing                     true
% 11.73/1.99  --smt_ac_axioms                         fast
% 11.73/1.99  --preprocessed_out                      false
% 11.73/1.99  --preprocessed_stats                    false
% 11.73/1.99  
% 11.73/1.99  ------ Abstraction refinement Options
% 11.73/1.99  
% 11.73/1.99  --abstr_ref                             []
% 11.73/1.99  --abstr_ref_prep                        false
% 11.73/1.99  --abstr_ref_until_sat                   false
% 11.73/1.99  --abstr_ref_sig_restrict                funpre
% 11.73/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/1.99  --abstr_ref_under                       []
% 11.73/1.99  
% 11.73/1.99  ------ SAT Options
% 11.73/1.99  
% 11.73/1.99  --sat_mode                              false
% 11.73/1.99  --sat_fm_restart_options                ""
% 11.73/1.99  --sat_gr_def                            false
% 11.73/1.99  --sat_epr_types                         true
% 11.73/1.99  --sat_non_cyclic_types                  false
% 11.73/1.99  --sat_finite_models                     false
% 11.73/1.99  --sat_fm_lemmas                         false
% 11.73/1.99  --sat_fm_prep                           false
% 11.73/1.99  --sat_fm_uc_incr                        true
% 11.73/1.99  --sat_out_model                         small
% 11.73/1.99  --sat_out_clauses                       false
% 11.73/1.99  
% 11.73/1.99  ------ QBF Options
% 11.73/1.99  
% 11.73/1.99  --qbf_mode                              false
% 11.73/1.99  --qbf_elim_univ                         false
% 11.73/1.99  --qbf_dom_inst                          none
% 11.73/1.99  --qbf_dom_pre_inst                      false
% 11.73/1.99  --qbf_sk_in                             false
% 11.73/1.99  --qbf_pred_elim                         true
% 11.73/1.99  --qbf_split                             512
% 11.73/1.99  
% 11.73/1.99  ------ BMC1 Options
% 11.73/1.99  
% 11.73/1.99  --bmc1_incremental                      false
% 11.73/1.99  --bmc1_axioms                           reachable_all
% 11.73/1.99  --bmc1_min_bound                        0
% 11.73/1.99  --bmc1_max_bound                        -1
% 11.73/1.99  --bmc1_max_bound_default                -1
% 11.73/1.99  --bmc1_symbol_reachability              true
% 11.73/1.99  --bmc1_property_lemmas                  false
% 11.73/1.99  --bmc1_k_induction                      false
% 11.73/1.99  --bmc1_non_equiv_states                 false
% 11.73/1.99  --bmc1_deadlock                         false
% 11.73/1.99  --bmc1_ucm                              false
% 11.73/1.99  --bmc1_add_unsat_core                   none
% 11.73/1.99  --bmc1_unsat_core_children              false
% 11.73/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/1.99  --bmc1_out_stat                         full
% 11.73/1.99  --bmc1_ground_init                      false
% 11.73/1.99  --bmc1_pre_inst_next_state              false
% 11.73/1.99  --bmc1_pre_inst_state                   false
% 11.73/1.99  --bmc1_pre_inst_reach_state             false
% 11.73/1.99  --bmc1_out_unsat_core                   false
% 11.73/1.99  --bmc1_aig_witness_out                  false
% 11.73/1.99  --bmc1_verbose                          false
% 11.73/1.99  --bmc1_dump_clauses_tptp                false
% 11.73/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.73/1.99  --bmc1_dump_file                        -
% 11.73/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.73/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.73/1.99  --bmc1_ucm_extend_mode                  1
% 11.73/1.99  --bmc1_ucm_init_mode                    2
% 11.73/1.99  --bmc1_ucm_cone_mode                    none
% 11.73/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.73/1.99  --bmc1_ucm_relax_model                  4
% 11.73/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.73/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/1.99  --bmc1_ucm_layered_model                none
% 11.73/1.99  --bmc1_ucm_max_lemma_size               10
% 11.73/1.99  
% 11.73/1.99  ------ AIG Options
% 11.73/1.99  
% 11.73/1.99  --aig_mode                              false
% 11.73/1.99  
% 11.73/1.99  ------ Instantiation Options
% 11.73/1.99  
% 11.73/1.99  --instantiation_flag                    true
% 11.73/1.99  --inst_sos_flag                         true
% 11.73/1.99  --inst_sos_phase                        true
% 11.73/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/1.99  --inst_lit_sel_side                     num_symb
% 11.73/1.99  --inst_solver_per_active                1400
% 11.73/1.99  --inst_solver_calls_frac                1.
% 11.73/1.99  --inst_passive_queue_type               priority_queues
% 11.73/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/1.99  --inst_passive_queues_freq              [25;2]
% 11.73/1.99  --inst_dismatching                      true
% 11.73/1.99  --inst_eager_unprocessed_to_passive     true
% 11.73/1.99  --inst_prop_sim_given                   true
% 11.73/1.99  --inst_prop_sim_new                     false
% 11.73/1.99  --inst_subs_new                         false
% 11.73/1.99  --inst_eq_res_simp                      false
% 11.73/1.99  --inst_subs_given                       false
% 11.73/1.99  --inst_orphan_elimination               true
% 11.73/1.99  --inst_learning_loop_flag               true
% 11.73/1.99  --inst_learning_start                   3000
% 11.73/1.99  --inst_learning_factor                  2
% 11.73/1.99  --inst_start_prop_sim_after_learn       3
% 11.73/1.99  --inst_sel_renew                        solver
% 11.73/1.99  --inst_lit_activity_flag                true
% 11.73/1.99  --inst_restr_to_given                   false
% 11.73/1.99  --inst_activity_threshold               500
% 11.73/1.99  --inst_out_proof                        true
% 11.73/1.99  
% 11.73/1.99  ------ Resolution Options
% 11.73/1.99  
% 11.73/1.99  --resolution_flag                       true
% 11.73/1.99  --res_lit_sel                           adaptive
% 11.73/1.99  --res_lit_sel_side                      none
% 11.73/1.99  --res_ordering                          kbo
% 11.73/1.99  --res_to_prop_solver                    active
% 11.73/1.99  --res_prop_simpl_new                    false
% 11.73/1.99  --res_prop_simpl_given                  true
% 11.73/1.99  --res_passive_queue_type                priority_queues
% 11.73/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/1.99  --res_passive_queues_freq               [15;5]
% 11.73/1.99  --res_forward_subs                      full
% 11.73/1.99  --res_backward_subs                     full
% 11.73/1.99  --res_forward_subs_resolution           true
% 11.73/1.99  --res_backward_subs_resolution          true
% 11.73/1.99  --res_orphan_elimination                true
% 11.73/1.99  --res_time_limit                        2.
% 11.73/1.99  --res_out_proof                         true
% 11.73/1.99  
% 11.73/1.99  ------ Superposition Options
% 11.73/1.99  
% 11.73/1.99  --superposition_flag                    true
% 11.73/1.99  --sup_passive_queue_type                priority_queues
% 11.73/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.73/1.99  --demod_completeness_check              fast
% 11.73/1.99  --demod_use_ground                      true
% 11.73/1.99  --sup_to_prop_solver                    passive
% 11.73/1.99  --sup_prop_simpl_new                    true
% 11.73/1.99  --sup_prop_simpl_given                  true
% 11.73/1.99  --sup_fun_splitting                     true
% 11.73/1.99  --sup_smt_interval                      50000
% 11.73/1.99  
% 11.73/1.99  ------ Superposition Simplification Setup
% 11.73/1.99  
% 11.73/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/1.99  --sup_immed_triv                        [TrivRules]
% 11.73/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_immed_bw_main                     []
% 11.73/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_input_bw                          []
% 11.73/1.99  
% 11.73/1.99  ------ Combination Options
% 11.73/1.99  
% 11.73/1.99  --comb_res_mult                         3
% 11.73/1.99  --comb_sup_mult                         2
% 11.73/1.99  --comb_inst_mult                        10
% 11.73/1.99  
% 11.73/1.99  ------ Debug Options
% 11.73/1.99  
% 11.73/1.99  --dbg_backtrace                         false
% 11.73/1.99  --dbg_dump_prop_clauses                 false
% 11.73/1.99  --dbg_dump_prop_clauses_file            -
% 11.73/1.99  --dbg_out_stat                          false
% 11.73/1.99  ------ Parsing...
% 11.73/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/1.99  ------ Proving...
% 11.73/1.99  ------ Problem Properties 
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  clauses                                 21
% 11.73/1.99  conjectures                             2
% 11.73/1.99  EPR                                     3
% 11.73/1.99  Horn                                    18
% 11.73/1.99  unary                                   10
% 11.73/1.99  binary                                  6
% 11.73/1.99  lits                                    39
% 11.73/1.99  lits eq                                 21
% 11.73/1.99  fd_pure                                 0
% 11.73/1.99  fd_pseudo                               0
% 11.73/1.99  fd_cond                                 2
% 11.73/1.99  fd_pseudo_cond                          1
% 11.73/1.99  AC symbols                              0
% 11.73/1.99  
% 11.73/1.99  ------ Schedule dynamic 5 is on 
% 11.73/1.99  
% 11.73/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  ------ 
% 11.73/1.99  Current options:
% 11.73/1.99  ------ 
% 11.73/1.99  
% 11.73/1.99  ------ Input Options
% 11.73/1.99  
% 11.73/1.99  --out_options                           all
% 11.73/1.99  --tptp_safe_out                         true
% 11.73/1.99  --problem_path                          ""
% 11.73/1.99  --include_path                          ""
% 11.73/1.99  --clausifier                            res/vclausify_rel
% 11.73/1.99  --clausifier_options                    ""
% 11.73/1.99  --stdin                                 false
% 11.73/1.99  --stats_out                             all
% 11.73/1.99  
% 11.73/1.99  ------ General Options
% 11.73/1.99  
% 11.73/1.99  --fof                                   false
% 11.73/1.99  --time_out_real                         305.
% 11.73/1.99  --time_out_virtual                      -1.
% 11.73/1.99  --symbol_type_check                     false
% 11.73/1.99  --clausify_out                          false
% 11.73/1.99  --sig_cnt_out                           false
% 11.73/1.99  --trig_cnt_out                          false
% 11.73/1.99  --trig_cnt_out_tolerance                1.
% 11.73/1.99  --trig_cnt_out_sk_spl                   false
% 11.73/1.99  --abstr_cl_out                          false
% 11.73/1.99  
% 11.73/1.99  ------ Global Options
% 11.73/1.99  
% 11.73/1.99  --schedule                              default
% 11.73/1.99  --add_important_lit                     false
% 11.73/1.99  --prop_solver_per_cl                    1000
% 11.73/1.99  --min_unsat_core                        false
% 11.73/1.99  --soft_assumptions                      false
% 11.73/1.99  --soft_lemma_size                       3
% 11.73/1.99  --prop_impl_unit_size                   0
% 11.73/1.99  --prop_impl_unit                        []
% 11.73/1.99  --share_sel_clauses                     true
% 11.73/1.99  --reset_solvers                         false
% 11.73/1.99  --bc_imp_inh                            [conj_cone]
% 11.73/1.99  --conj_cone_tolerance                   3.
% 11.73/1.99  --extra_neg_conj                        none
% 11.73/1.99  --large_theory_mode                     true
% 11.73/1.99  --prolific_symb_bound                   200
% 11.73/1.99  --lt_threshold                          2000
% 11.73/1.99  --clause_weak_htbl                      true
% 11.73/1.99  --gc_record_bc_elim                     false
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing Options
% 11.73/1.99  
% 11.73/1.99  --preprocessing_flag                    true
% 11.73/1.99  --time_out_prep_mult                    0.1
% 11.73/1.99  --splitting_mode                        input
% 11.73/1.99  --splitting_grd                         true
% 11.73/1.99  --splitting_cvd                         false
% 11.73/1.99  --splitting_cvd_svl                     false
% 11.73/1.99  --splitting_nvd                         32
% 11.73/1.99  --sub_typing                            true
% 11.73/1.99  --prep_gs_sim                           true
% 11.73/1.99  --prep_unflatten                        true
% 11.73/1.99  --prep_res_sim                          true
% 11.73/1.99  --prep_upred                            true
% 11.73/1.99  --prep_sem_filter                       exhaustive
% 11.73/1.99  --prep_sem_filter_out                   false
% 11.73/1.99  --pred_elim                             true
% 11.73/1.99  --res_sim_input                         true
% 11.73/1.99  --eq_ax_congr_red                       true
% 11.73/1.99  --pure_diseq_elim                       true
% 11.73/1.99  --brand_transform                       false
% 11.73/1.99  --non_eq_to_eq                          false
% 11.73/1.99  --prep_def_merge                        true
% 11.73/1.99  --prep_def_merge_prop_impl              false
% 11.73/1.99  --prep_def_merge_mbd                    true
% 11.73/1.99  --prep_def_merge_tr_red                 false
% 11.73/1.99  --prep_def_merge_tr_cl                  false
% 11.73/1.99  --smt_preprocessing                     true
% 11.73/1.99  --smt_ac_axioms                         fast
% 11.73/1.99  --preprocessed_out                      false
% 11.73/1.99  --preprocessed_stats                    false
% 11.73/1.99  
% 11.73/1.99  ------ Abstraction refinement Options
% 11.73/1.99  
% 11.73/1.99  --abstr_ref                             []
% 11.73/1.99  --abstr_ref_prep                        false
% 11.73/1.99  --abstr_ref_until_sat                   false
% 11.73/1.99  --abstr_ref_sig_restrict                funpre
% 11.73/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/1.99  --abstr_ref_under                       []
% 11.73/1.99  
% 11.73/1.99  ------ SAT Options
% 11.73/1.99  
% 11.73/1.99  --sat_mode                              false
% 11.73/1.99  --sat_fm_restart_options                ""
% 11.73/1.99  --sat_gr_def                            false
% 11.73/1.99  --sat_epr_types                         true
% 11.73/1.99  --sat_non_cyclic_types                  false
% 11.73/1.99  --sat_finite_models                     false
% 11.73/1.99  --sat_fm_lemmas                         false
% 11.73/1.99  --sat_fm_prep                           false
% 11.73/1.99  --sat_fm_uc_incr                        true
% 11.73/1.99  --sat_out_model                         small
% 11.73/1.99  --sat_out_clauses                       false
% 11.73/1.99  
% 11.73/1.99  ------ QBF Options
% 11.73/1.99  
% 11.73/1.99  --qbf_mode                              false
% 11.73/1.99  --qbf_elim_univ                         false
% 11.73/1.99  --qbf_dom_inst                          none
% 11.73/1.99  --qbf_dom_pre_inst                      false
% 11.73/1.99  --qbf_sk_in                             false
% 11.73/1.99  --qbf_pred_elim                         true
% 11.73/1.99  --qbf_split                             512
% 11.73/1.99  
% 11.73/1.99  ------ BMC1 Options
% 11.73/1.99  
% 11.73/1.99  --bmc1_incremental                      false
% 11.73/1.99  --bmc1_axioms                           reachable_all
% 11.73/1.99  --bmc1_min_bound                        0
% 11.73/1.99  --bmc1_max_bound                        -1
% 11.73/1.99  --bmc1_max_bound_default                -1
% 11.73/1.99  --bmc1_symbol_reachability              true
% 11.73/1.99  --bmc1_property_lemmas                  false
% 11.73/1.99  --bmc1_k_induction                      false
% 11.73/1.99  --bmc1_non_equiv_states                 false
% 11.73/1.99  --bmc1_deadlock                         false
% 11.73/1.99  --bmc1_ucm                              false
% 11.73/1.99  --bmc1_add_unsat_core                   none
% 11.73/1.99  --bmc1_unsat_core_children              false
% 11.73/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/1.99  --bmc1_out_stat                         full
% 11.73/1.99  --bmc1_ground_init                      false
% 11.73/1.99  --bmc1_pre_inst_next_state              false
% 11.73/1.99  --bmc1_pre_inst_state                   false
% 11.73/1.99  --bmc1_pre_inst_reach_state             false
% 11.73/1.99  --bmc1_out_unsat_core                   false
% 11.73/1.99  --bmc1_aig_witness_out                  false
% 11.73/1.99  --bmc1_verbose                          false
% 11.73/1.99  --bmc1_dump_clauses_tptp                false
% 11.73/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.73/1.99  --bmc1_dump_file                        -
% 11.73/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.73/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.73/1.99  --bmc1_ucm_extend_mode                  1
% 11.73/1.99  --bmc1_ucm_init_mode                    2
% 11.73/1.99  --bmc1_ucm_cone_mode                    none
% 11.73/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.73/1.99  --bmc1_ucm_relax_model                  4
% 11.73/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.73/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/1.99  --bmc1_ucm_layered_model                none
% 11.73/1.99  --bmc1_ucm_max_lemma_size               10
% 11.73/1.99  
% 11.73/1.99  ------ AIG Options
% 11.73/1.99  
% 11.73/1.99  --aig_mode                              false
% 11.73/1.99  
% 11.73/1.99  ------ Instantiation Options
% 11.73/1.99  
% 11.73/1.99  --instantiation_flag                    true
% 11.73/1.99  --inst_sos_flag                         true
% 11.73/1.99  --inst_sos_phase                        true
% 11.73/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/1.99  --inst_lit_sel_side                     none
% 11.73/1.99  --inst_solver_per_active                1400
% 11.73/1.99  --inst_solver_calls_frac                1.
% 11.73/1.99  --inst_passive_queue_type               priority_queues
% 11.73/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/1.99  --inst_passive_queues_freq              [25;2]
% 11.73/1.99  --inst_dismatching                      true
% 11.73/1.99  --inst_eager_unprocessed_to_passive     true
% 11.73/1.99  --inst_prop_sim_given                   true
% 11.73/1.99  --inst_prop_sim_new                     false
% 11.73/1.99  --inst_subs_new                         false
% 11.73/1.99  --inst_eq_res_simp                      false
% 11.73/1.99  --inst_subs_given                       false
% 11.73/1.99  --inst_orphan_elimination               true
% 11.73/1.99  --inst_learning_loop_flag               true
% 11.73/1.99  --inst_learning_start                   3000
% 11.73/1.99  --inst_learning_factor                  2
% 11.73/1.99  --inst_start_prop_sim_after_learn       3
% 11.73/1.99  --inst_sel_renew                        solver
% 11.73/1.99  --inst_lit_activity_flag                true
% 11.73/1.99  --inst_restr_to_given                   false
% 11.73/1.99  --inst_activity_threshold               500
% 11.73/1.99  --inst_out_proof                        true
% 11.73/1.99  
% 11.73/1.99  ------ Resolution Options
% 11.73/1.99  
% 11.73/1.99  --resolution_flag                       false
% 11.73/1.99  --res_lit_sel                           adaptive
% 11.73/1.99  --res_lit_sel_side                      none
% 11.73/1.99  --res_ordering                          kbo
% 11.73/1.99  --res_to_prop_solver                    active
% 11.73/1.99  --res_prop_simpl_new                    false
% 11.73/1.99  --res_prop_simpl_given                  true
% 11.73/1.99  --res_passive_queue_type                priority_queues
% 11.73/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/1.99  --res_passive_queues_freq               [15;5]
% 11.73/1.99  --res_forward_subs                      full
% 11.73/1.99  --res_backward_subs                     full
% 11.73/1.99  --res_forward_subs_resolution           true
% 11.73/1.99  --res_backward_subs_resolution          true
% 11.73/1.99  --res_orphan_elimination                true
% 11.73/1.99  --res_time_limit                        2.
% 11.73/1.99  --res_out_proof                         true
% 11.73/1.99  
% 11.73/1.99  ------ Superposition Options
% 11.73/1.99  
% 11.73/1.99  --superposition_flag                    true
% 11.73/1.99  --sup_passive_queue_type                priority_queues
% 11.73/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.73/1.99  --demod_completeness_check              fast
% 11.73/1.99  --demod_use_ground                      true
% 11.73/1.99  --sup_to_prop_solver                    passive
% 11.73/1.99  --sup_prop_simpl_new                    true
% 11.73/1.99  --sup_prop_simpl_given                  true
% 11.73/1.99  --sup_fun_splitting                     true
% 11.73/1.99  --sup_smt_interval                      50000
% 11.73/1.99  
% 11.73/1.99  ------ Superposition Simplification Setup
% 11.73/1.99  
% 11.73/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/1.99  --sup_immed_triv                        [TrivRules]
% 11.73/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_immed_bw_main                     []
% 11.73/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/1.99  --sup_input_bw                          []
% 11.73/1.99  
% 11.73/1.99  ------ Combination Options
% 11.73/1.99  
% 11.73/1.99  --comb_res_mult                         3
% 11.73/1.99  --comb_sup_mult                         2
% 11.73/1.99  --comb_inst_mult                        10
% 11.73/1.99  
% 11.73/1.99  ------ Debug Options
% 11.73/1.99  
% 11.73/1.99  --dbg_backtrace                         false
% 11.73/1.99  --dbg_dump_prop_clauses                 false
% 11.73/1.99  --dbg_dump_prop_clauses_file            -
% 11.73/1.99  --dbg_out_stat                          false
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  ------ Proving...
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  % SZS status Theorem for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99   Resolution empty clause
% 11.73/1.99  
% 11.73/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  fof(f14,axiom,(
% 11.73/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f37,plain,(
% 11.73/1.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.73/1.99    inference(nnf_transformation,[],[f14])).
% 11.73/1.99  
% 11.73/1.99  fof(f62,plain,(
% 11.73/1.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f37])).
% 11.73/1.99  
% 11.73/1.99  fof(f7,axiom,(
% 11.73/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f54,plain,(
% 11.73/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f7])).
% 11.73/1.99  
% 11.73/1.99  fof(f8,axiom,(
% 11.73/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f55,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f8])).
% 11.73/1.99  
% 11.73/1.99  fof(f9,axiom,(
% 11.73/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f56,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f9])).
% 11.73/1.99  
% 11.73/1.99  fof(f10,axiom,(
% 11.73/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f57,plain,(
% 11.73/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f10])).
% 11.73/1.99  
% 11.73/1.99  fof(f11,axiom,(
% 11.73/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f58,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f11])).
% 11.73/1.99  
% 11.73/1.99  fof(f12,axiom,(
% 11.73/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f59,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f12])).
% 11.73/1.99  
% 11.73/1.99  fof(f13,axiom,(
% 11.73/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f60,plain,(
% 11.73/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f13])).
% 11.73/1.99  
% 11.73/1.99  fof(f80,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f59,f60])).
% 11.73/1.99  
% 11.73/1.99  fof(f81,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f58,f80])).
% 11.73/1.99  
% 11.73/1.99  fof(f82,plain,(
% 11.73/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f57,f81])).
% 11.73/1.99  
% 11.73/1.99  fof(f83,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f56,f82])).
% 11.73/1.99  
% 11.73/1.99  fof(f84,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f55,f83])).
% 11.73/1.99  
% 11.73/1.99  fof(f87,plain,(
% 11.73/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f54,f84])).
% 11.73/1.99  
% 11.73/1.99  fof(f90,plain,(
% 11.73/1.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f62,f87])).
% 11.73/1.99  
% 11.73/1.99  fof(f18,axiom,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f28,plain,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 11.73/1.99    inference(ennf_transformation,[],[f18])).
% 11.73/1.99  
% 11.73/1.99  fof(f41,plain,(
% 11.73/1.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 11.73/1.99    inference(nnf_transformation,[],[f28])).
% 11.73/1.99  
% 11.73/1.99  fof(f42,plain,(
% 11.73/1.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.73/1.99    inference(rectify,[],[f41])).
% 11.73/1.99  
% 11.73/1.99  fof(f44,plain,(
% 11.73/1.99    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f43,plain,(
% 11.73/1.99    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f45,plain,(
% 11.73/1.99    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).
% 11.73/1.99  
% 11.73/1.99  fof(f70,plain,(
% 11.73/1.99    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f45])).
% 11.73/1.99  
% 11.73/1.99  fof(f5,axiom,(
% 11.73/1.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f27,plain,(
% 11.73/1.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.73/1.99    inference(ennf_transformation,[],[f5])).
% 11.73/1.99  
% 11.73/1.99  fof(f52,plain,(
% 11.73/1.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f27])).
% 11.73/1.99  
% 11.73/1.99  fof(f24,conjecture,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f25,negated_conjecture,(
% 11.73/1.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 11.73/1.99    inference(negated_conjecture,[],[f24])).
% 11.73/1.99  
% 11.73/1.99  fof(f36,plain,(
% 11.73/1.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 11.73/1.99    inference(ennf_transformation,[],[f25])).
% 11.73/1.99  
% 11.73/1.99  fof(f46,plain,(
% 11.73/1.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f47,plain,(
% 11.73/1.99    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f46])).
% 11.73/1.99  
% 11.73/1.99  fof(f78,plain,(
% 11.73/1.99    v1_relat_1(sK3)),
% 11.73/1.99    inference(cnf_transformation,[],[f47])).
% 11.73/1.99  
% 11.73/1.99  fof(f19,axiom,(
% 11.73/1.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f29,plain,(
% 11.73/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.73/1.99    inference(ennf_transformation,[],[f19])).
% 11.73/1.99  
% 11.73/1.99  fof(f30,plain,(
% 11.73/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.73/1.99    inference(flattening,[],[f29])).
% 11.73/1.99  
% 11.73/1.99  fof(f72,plain,(
% 11.73/1.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f30])).
% 11.73/1.99  
% 11.73/1.99  fof(f20,axiom,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f31,plain,(
% 11.73/1.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.73/1.99    inference(ennf_transformation,[],[f20])).
% 11.73/1.99  
% 11.73/1.99  fof(f73,plain,(
% 11.73/1.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f31])).
% 11.73/1.99  
% 11.73/1.99  fof(f17,axiom,(
% 11.73/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f68,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f17])).
% 11.73/1.99  
% 11.73/1.99  fof(f85,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f68,f84])).
% 11.73/1.99  
% 11.73/1.99  fof(f94,plain,(
% 11.73/1.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f73,f85])).
% 11.73/1.99  
% 11.73/1.99  fof(f4,axiom,(
% 11.73/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f51,plain,(
% 11.73/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f4])).
% 11.73/1.99  
% 11.73/1.99  fof(f23,axiom,(
% 11.73/1.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f76,plain,(
% 11.73/1.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.73/1.99    inference(cnf_transformation,[],[f23])).
% 11.73/1.99  
% 11.73/1.99  fof(f22,axiom,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f34,plain,(
% 11.73/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.99    inference(ennf_transformation,[],[f22])).
% 11.73/1.99  
% 11.73/1.99  fof(f35,plain,(
% 11.73/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.99    inference(flattening,[],[f34])).
% 11.73/1.99  
% 11.73/1.99  fof(f75,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f35])).
% 11.73/1.99  
% 11.73/1.99  fof(f77,plain,(
% 11.73/1.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.73/1.99    inference(cnf_transformation,[],[f23])).
% 11.73/1.99  
% 11.73/1.99  fof(f16,axiom,(
% 11.73/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f40,plain,(
% 11.73/1.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.73/1.99    inference(nnf_transformation,[],[f16])).
% 11.73/1.99  
% 11.73/1.99  fof(f66,plain,(
% 11.73/1.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f40])).
% 11.73/1.99  
% 11.73/1.99  fof(f2,axiom,(
% 11.73/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f49,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f2])).
% 11.73/1.99  
% 11.73/1.99  fof(f86,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f49,f85])).
% 11.73/1.99  
% 11.73/1.99  fof(f93,plain,(
% 11.73/1.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f66,f86,f87,f87,f87])).
% 11.73/1.99  
% 11.73/1.99  fof(f97,plain,(
% 11.73/1.99    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.73/1.99    inference(equality_resolution,[],[f93])).
% 11.73/1.99  
% 11.73/1.99  fof(f1,axiom,(
% 11.73/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f26,plain,(
% 11.73/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.73/1.99    inference(rectify,[],[f1])).
% 11.73/1.99  
% 11.73/1.99  fof(f48,plain,(
% 11.73/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.73/1.99    inference(cnf_transformation,[],[f26])).
% 11.73/1.99  
% 11.73/1.99  fof(f88,plain,(
% 11.73/1.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 11.73/1.99    inference(definition_unfolding,[],[f48,f85])).
% 11.73/1.99  
% 11.73/1.99  fof(f6,axiom,(
% 11.73/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f53,plain,(
% 11.73/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.73/1.99    inference(cnf_transformation,[],[f6])).
% 11.73/1.99  
% 11.73/1.99  fof(f3,axiom,(
% 11.73/1.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f50,plain,(
% 11.73/1.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.73/1.99    inference(cnf_transformation,[],[f3])).
% 11.73/1.99  
% 11.73/1.99  fof(f89,plain,(
% 11.73/1.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f50,f85])).
% 11.73/1.99  
% 11.73/1.99  fof(f15,axiom,(
% 11.73/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f38,plain,(
% 11.73/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/1.99    inference(nnf_transformation,[],[f15])).
% 11.73/1.99  
% 11.73/1.99  fof(f39,plain,(
% 11.73/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/1.99    inference(flattening,[],[f38])).
% 11.73/1.99  
% 11.73/1.99  fof(f65,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.73/1.99    inference(cnf_transformation,[],[f39])).
% 11.73/1.99  
% 11.73/1.99  fof(f95,plain,(
% 11.73/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.73/1.99    inference(equality_resolution,[],[f65])).
% 11.73/1.99  
% 11.73/1.99  fof(f79,plain,(
% 11.73/1.99    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 11.73/1.99    inference(cnf_transformation,[],[f47])).
% 11.73/1.99  
% 11.73/1.99  fof(f67,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 11.73/1.99    inference(cnf_transformation,[],[f40])).
% 11.73/1.99  
% 11.73/1.99  fof(f92,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 11.73/1.99    inference(definition_unfolding,[],[f67,f86,f87,f87,f87])).
% 11.73/1.99  
% 11.73/1.99  fof(f21,axiom,(
% 11.73/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 11.73/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f32,plain,(
% 11.73/1.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.99    inference(ennf_transformation,[],[f21])).
% 11.73/1.99  
% 11.73/1.99  fof(f33,plain,(
% 11.73/1.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.73/1.99    inference(flattening,[],[f32])).
% 11.73/1.99  
% 11.73/1.99  fof(f74,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f33])).
% 11.73/1.99  
% 11.73/1.99  fof(f64,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.73/1.99    inference(cnf_transformation,[],[f39])).
% 11.73/1.99  
% 11.73/1.99  fof(f96,plain,(
% 11.73/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.73/1.99    inference(equality_resolution,[],[f64])).
% 11.73/1.99  
% 11.73/1.99  cnf(c_5,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,X1)
% 11.73/1.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.73/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_119,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,X1)
% 11.73/1.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.73/1.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_13,plain,
% 11.73/1.99      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_224,plain,
% 11.73/1.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 11.73/1.99      | v1_relat_1(X2)
% 11.73/1.99      | X2 != X1
% 11.73/1.99      | sK0(X2) != X0 ),
% 11.73/1.99      inference(resolution_lifted,[status(thm)],[c_119,c_13]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_225,plain,
% 11.73/1.99      ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0)
% 11.73/1.99      | v1_relat_1(X0) ),
% 11.73/1.99      inference(unflattening,[status(thm)],[c_224]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_758,plain,
% 11.73/1.99      ( r1_tarski(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = iProver_top
% 11.73/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3,plain,
% 11.73/1.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_766,plain,
% 11.73/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1011,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_758,c_766]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_22,negated_conjecture,
% 11.73/1.99      ( v1_relat_1(sK3) ),
% 11.73/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_760,plain,
% 11.73/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_15,plain,
% 11.73/1.99      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_764,plain,
% 11.73/1.99      ( v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(X1) != iProver_top
% 11.73/1.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_16,plain,
% 11.73/1.99      ( ~ v1_relat_1(X0)
% 11.73/1.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_763,plain,
% 11.73/1.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 11.73/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1121,plain,
% 11.73/1.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_764,c_763]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2212,plain,
% 11.73/1.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 11.73/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_760,c_1121]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2495,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1011,c_2212]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2,plain,
% 11.73/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_767,plain,
% 11.73/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_20,plain,
% 11.73/1.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_18,plain,
% 11.73/1.99      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 11.73/1.99      | ~ v1_relat_1(X0)
% 11.73/1.99      | ~ v1_relat_1(X1)
% 11.73/1.99      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_761,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 11.73/1.99      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 11.73/1.99      | v1_relat_1(X1) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1195,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 11.73/1.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_20,c_761]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19,plain,
% 11.73/1.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1197,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(light_normalisation,[status(thm)],[c_1195,c_19]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1226,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_767,c_1197]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1285,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_760,c_1226]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1593,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1011,c_1285]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_11,plain,
% 11.73/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_0,plain,
% 11.73/1.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_4,plain,
% 11.73/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_768,plain,
% 11.73/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.73/1.99      inference(demodulation,[status(thm)],[c_11,c_0,c_4]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_7246,plain,
% 11.73/1.99      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1593,c_768]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_26071,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 11.73/1.99      inference(light_normalisation,[status(thm)],[c_2495,c_7246]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1,plain,
% 11.73/1.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_7,plain,
% 11.73/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_26072,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.73/1.99      inference(demodulation,[status(thm)],[c_26071,c_1,c_7]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_21,negated_conjecture,
% 11.73/1.99      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 11.73/1.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 11.73/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_45,plain,
% 11.73/1.99      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_10,plain,
% 11.73/1.99      ( X0 = X1
% 11.73/1.99      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 11.73/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_46,plain,
% 11.73/1.99      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 11.73/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_572,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_786,plain,
% 11.73/1.99      ( k5_relat_1(sK3,k1_xboole_0) != X0
% 11.73/1.99      | k1_xboole_0 != X0
% 11.73/1.99      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_572]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_787,plain,
% 11.73/1.99      ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 11.73/1.99      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
% 11.73/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_786]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_807,plain,
% 11.73/1.99      ( k5_relat_1(k1_xboole_0,sK3) != X0
% 11.73/1.99      | k1_xboole_0 != X0
% 11.73/1.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_572]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_808,plain,
% 11.73/1.99      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 11.73/1.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
% 11.73/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_807]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2213,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 11.73/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1011,c_1121]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19638,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_760,c_2213]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_17,plain,
% 11.73/1.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 11.73/1.99      | ~ v1_relat_1(X0)
% 11.73/1.99      | ~ v1_relat_1(X1)
% 11.73/1.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_762,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 11.73/1.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1205,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 11.73/1.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_19,c_762]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1207,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 11.73/1.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(light_normalisation,[status(thm)],[c_1205,c_20]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1232,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 11.73/1.99      | v1_relat_1(X0) != iProver_top
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_767,c_1207]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1365,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0
% 11.73/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_760,c_1232]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1592,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1011,c_1365]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_6392,plain,
% 11.73/1.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1592,c_768]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19642,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 11.73/1.99      inference(light_normalisation,[status(thm)],[c_19638,c_6392]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_8,plain,
% 11.73/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19643,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0
% 11.73/1.99      | k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 11.73/1.99      inference(demodulation,[status(thm)],[c_19642,c_1,c_8]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19697,plain,
% 11.73/1.99      ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_19643,c_768]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_26073,plain,
% 11.73/1.99      ( k6_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)) = k1_xboole_0 ),
% 11.73/1.99      inference(global_propositional_subsumption,
% 11.73/1.99                [status(thm)],
% 11.73/1.99                [c_26072,c_21,c_45,c_46,c_787,c_808,c_19697]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_26076,plain,
% 11.73/1.99      ( $false ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_26073,c_768]) ).
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  ------                               Statistics
% 11.73/1.99  
% 11.73/1.99  ------ General
% 11.73/1.99  
% 11.73/1.99  abstr_ref_over_cycles:                  0
% 11.73/1.99  abstr_ref_under_cycles:                 0
% 11.73/1.99  gc_basic_clause_elim:                   0
% 11.73/1.99  forced_gc_time:                         0
% 11.73/1.99  parsing_time:                           0.008
% 11.73/1.99  unif_index_cands_time:                  0.
% 11.73/1.99  unif_index_add_time:                    0.
% 11.73/1.99  orderings_time:                         0.
% 11.73/1.99  out_proof_time:                         0.015
% 11.73/1.99  total_time:                             1.315
% 11.73/1.99  num_of_symbols:                         47
% 11.73/1.99  num_of_terms:                           20612
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing
% 11.73/1.99  
% 11.73/1.99  num_of_splits:                          0
% 11.73/1.99  num_of_split_atoms:                     0
% 11.73/1.99  num_of_reused_defs:                     0
% 11.73/1.99  num_eq_ax_congr_red:                    10
% 11.73/1.99  num_of_sem_filtered_clauses:            1
% 11.73/1.99  num_of_subtypes:                        0
% 11.73/1.99  monotx_restored_types:                  0
% 11.73/1.99  sat_num_of_epr_types:                   0
% 11.73/1.99  sat_num_of_non_cyclic_types:            0
% 11.73/1.99  sat_guarded_non_collapsed_types:        0
% 11.73/1.99  num_pure_diseq_elim:                    0
% 11.73/1.99  simp_replaced_by:                       0
% 11.73/1.99  res_preprocessed:                       111
% 11.73/1.99  prep_upred:                             0
% 11.73/1.99  prep_unflattend:                        24
% 11.73/1.99  smt_new_axioms:                         0
% 11.73/1.99  pred_elim_cands:                        2
% 11.73/1.99  pred_elim:                              1
% 11.73/1.99  pred_elim_cl:                           2
% 11.73/1.99  pred_elim_cycles:                       3
% 11.73/1.99  merged_defs:                            2
% 11.73/1.99  merged_defs_ncl:                        0
% 11.73/1.99  bin_hyper_res:                          2
% 11.73/1.99  prep_cycles:                            4
% 11.73/1.99  pred_elim_time:                         0.003
% 11.73/1.99  splitting_time:                         0.
% 11.73/1.99  sem_filter_time:                        0.
% 11.73/1.99  monotx_time:                            0.
% 11.73/1.99  subtype_inf_time:                       0.
% 11.73/1.99  
% 11.73/1.99  ------ Problem properties
% 11.73/1.99  
% 11.73/1.99  clauses:                                21
% 11.73/1.99  conjectures:                            2
% 11.73/1.99  epr:                                    3
% 11.73/1.99  horn:                                   18
% 11.73/1.99  ground:                                 4
% 11.73/1.99  unary:                                  10
% 11.73/1.99  binary:                                 6
% 11.73/1.99  lits:                                   39
% 11.73/1.99  lits_eq:                                21
% 11.73/1.99  fd_pure:                                0
% 11.73/1.99  fd_pseudo:                              0
% 11.73/1.99  fd_cond:                                2
% 11.73/1.99  fd_pseudo_cond:                         1
% 11.73/1.99  ac_symbols:                             0
% 11.73/1.99  
% 11.73/1.99  ------ Propositional Solver
% 11.73/1.99  
% 11.73/1.99  prop_solver_calls:                      37
% 11.73/1.99  prop_fast_solver_calls:                 1904
% 11.73/1.99  smt_solver_calls:                       0
% 11.73/1.99  smt_fast_solver_calls:                  0
% 11.73/1.99  prop_num_of_clauses:                    9466
% 11.73/1.99  prop_preprocess_simplified:             16878
% 11.73/1.99  prop_fo_subsumed:                       27
% 11.73/1.99  prop_solver_time:                       0.
% 11.73/1.99  smt_solver_time:                        0.
% 11.73/1.99  smt_fast_solver_time:                   0.
% 11.73/1.99  prop_fast_solver_time:                  0.
% 11.73/1.99  prop_unsat_core_time:                   0.
% 11.73/1.99  
% 11.73/1.99  ------ QBF
% 11.73/1.99  
% 11.73/1.99  qbf_q_res:                              0
% 11.73/1.99  qbf_num_tautologies:                    0
% 11.73/1.99  qbf_prep_cycles:                        0
% 11.73/1.99  
% 11.73/1.99  ------ BMC1
% 11.73/1.99  
% 11.73/1.99  bmc1_current_bound:                     -1
% 11.73/1.99  bmc1_last_solved_bound:                 -1
% 11.73/1.99  bmc1_unsat_core_size:                   -1
% 11.73/1.99  bmc1_unsat_core_parents_size:           -1
% 11.73/1.99  bmc1_merge_next_fun:                    0
% 11.73/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.73/1.99  
% 11.73/1.99  ------ Instantiation
% 11.73/1.99  
% 11.73/1.99  inst_num_of_clauses:                    4521
% 11.73/1.99  inst_num_in_passive:                    624
% 11.73/1.99  inst_num_in_active:                     1785
% 11.73/1.99  inst_num_in_unprocessed:                2112
% 11.73/1.99  inst_num_of_loops:                      2220
% 11.73/1.99  inst_num_of_learning_restarts:          0
% 11.73/1.99  inst_num_moves_active_passive:          430
% 11.73/1.99  inst_lit_activity:                      0
% 11.73/1.99  inst_lit_activity_moves:                0
% 11.73/1.99  inst_num_tautologies:                   0
% 11.73/1.99  inst_num_prop_implied:                  0
% 11.73/1.99  inst_num_existing_simplified:           0
% 11.73/1.99  inst_num_eq_res_simplified:             0
% 11.73/1.99  inst_num_child_elim:                    0
% 11.73/1.99  inst_num_of_dismatching_blockings:      2693
% 11.73/1.99  inst_num_of_non_proper_insts:           8002
% 11.73/1.99  inst_num_of_duplicates:                 0
% 11.73/1.99  inst_inst_num_from_inst_to_res:         0
% 11.73/1.99  inst_dismatching_checking_time:         0.
% 11.73/1.99  
% 11.73/1.99  ------ Resolution
% 11.73/1.99  
% 11.73/1.99  res_num_of_clauses:                     0
% 11.73/1.99  res_num_in_passive:                     0
% 11.73/1.99  res_num_in_active:                      0
% 11.73/1.99  res_num_of_loops:                       115
% 11.73/1.99  res_forward_subset_subsumed:            384
% 11.73/1.99  res_backward_subset_subsumed:           18
% 11.73/1.99  res_forward_subsumed:                   0
% 11.73/1.99  res_backward_subsumed:                  0
% 11.73/1.99  res_forward_subsumption_resolution:     0
% 11.73/1.99  res_backward_subsumption_resolution:    0
% 11.73/1.99  res_clause_to_clause_subsumption:       7646
% 11.73/1.99  res_orphan_elimination:                 0
% 11.73/1.99  res_tautology_del:                      333
% 11.73/1.99  res_num_eq_res_simplified:              0
% 11.73/1.99  res_num_sel_changes:                    0
% 11.73/1.99  res_moves_from_active_to_pass:          0
% 11.73/1.99  
% 11.73/1.99  ------ Superposition
% 11.73/1.99  
% 11.73/1.99  sup_time_total:                         0.
% 11.73/1.99  sup_time_generating:                    0.
% 11.73/1.99  sup_time_sim_full:                      0.
% 11.73/1.99  sup_time_sim_immed:                     0.
% 11.73/1.99  
% 11.73/1.99  sup_num_of_clauses:                     539
% 11.73/1.99  sup_num_in_active:                      345
% 11.73/1.99  sup_num_in_passive:                     194
% 11.73/1.99  sup_num_of_loops:                       442
% 11.73/1.99  sup_fw_superposition:                   890
% 11.73/1.99  sup_bw_superposition:                   312
% 11.73/1.99  sup_immediate_simplified:               144
% 11.73/1.99  sup_given_eliminated:                   23
% 11.73/1.99  comparisons_done:                       0
% 11.73/1.99  comparisons_avoided:                    5
% 11.73/1.99  
% 11.73/1.99  ------ Simplifications
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  sim_fw_subset_subsumed:                 97
% 11.73/1.99  sim_bw_subset_subsumed:                 377
% 11.73/1.99  sim_fw_subsumed:                        31
% 11.73/1.99  sim_bw_subsumed:                        60
% 11.73/1.99  sim_fw_subsumption_res:                 0
% 11.73/1.99  sim_bw_subsumption_res:                 0
% 11.73/1.99  sim_tautology_del:                      2
% 11.73/1.99  sim_eq_tautology_del:                   13
% 11.73/1.99  sim_eq_res_simp:                        1
% 11.73/1.99  sim_fw_demodulated:                     25
% 11.73/1.99  sim_bw_demodulated:                     54
% 11.73/1.99  sim_light_normalised:                   46
% 11.73/1.99  sim_joinable_taut:                      0
% 11.73/1.99  sim_joinable_simp:                      0
% 11.73/1.99  sim_ac_normalised:                      0
% 11.73/1.99  sim_smt_subsumption:                    0
% 11.73/1.99  
%------------------------------------------------------------------------------
