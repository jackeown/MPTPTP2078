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
% DateTime   : Thu Dec  3 11:44:18 EST 2020

% Result     : Theorem 55.36s
% Output     : CNFRefutation 55.36s
% Verified   : 
% Statistics : Number of formulae       :  169 (1537 expanded)
%              Number of clauses        :   76 ( 178 expanded)
%              Number of leaves         :   29 ( 466 expanded)
%              Depth                    :   21
%              Number of atoms          :  329 (2108 expanded)
%              Number of equality atoms :  229 (1697 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f37,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f45,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f45])).

fof(f77,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f43,f42])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f86])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f84])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f65,f85,f86,f86,f86])).

fof(f97,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f84])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f84])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f62,f84,f84,f84])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) ),
    inference(definition_unfolding,[],[f63,f85,f85])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f64,f85,f85])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f66,f85,f86,f86,f86])).

fof(f78,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_545,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_551,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_554,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_555,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1165,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_555])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_641,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11,c_0,c_4])).

cnf(c_1270,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_641])).

cnf(c_1406,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_1270])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_549,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_548,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1280,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_548])).

cnf(c_2954,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_1280])).

cnf(c_51127,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_545,c_2954])).

cnf(c_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_547,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1377,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_547])).

cnf(c_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1391,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1377,c_20])).

cnf(c_1486,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1391,c_1406])).

cnf(c_1487,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1486])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_556,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1493,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1487,c_556])).

cnf(c_1498,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_545,c_1493])).

cnf(c_51132,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_51127,c_1498])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1281,plain,
    ( k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = sK3 ),
    inference(superposition,[status(thm)],[c_545,c_548])).

cnf(c_7,plain,
    ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_9,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_633,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(demodulation,[status(thm)],[c_7,c_9])).

cnf(c_635,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(demodulation,[status(thm)],[c_633,c_0])).

cnf(c_2217,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),X0) = k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1281,c_635])).

cnf(c_2219,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(k5_xboole_0(sK3,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_2217,c_1281])).

cnf(c_2220,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2219,c_4])).

cnf(c_51133,plain,
    ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51132,c_1,c_2220])).

cnf(c_2066,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1280])).

cnf(c_2953,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1406,c_2066])).

cnf(c_18,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_546,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_774,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_546])).

cnf(c_788,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_774,c_19])).

cnf(c_1461,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_1406])).

cnf(c_1462,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1461])).

cnf(c_1468,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1462,c_556])).

cnf(c_1473,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_545,c_1468])).

cnf(c_2970,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2953,c_1473])).

cnf(c_2516,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1)))))) = k5_relat_1(sK3,k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_2066])).

cnf(c_2728,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0)))))) = k5_relat_1(sK3,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_2516])).

cnf(c_2777,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_545,c_2728])).

cnf(c_8,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_632,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_7,c_8])).

cnf(c_638,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_632,c_0])).

cnf(c_2990,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
    inference(superposition,[status(thm)],[c_2777,c_638])).

cnf(c_2992,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_2990,c_2777])).

cnf(c_2993,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2992,c_4])).

cnf(c_3392,plain,
    ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2970,c_1,c_2993])).

cnf(c_185,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_763,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_764,plain,
    ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_705,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_706,plain,
    ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_10,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_45,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51133,c_3392,c_764,c_706,c_46,c_45,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 55.36/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.36/7.50  
% 55.36/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.36/7.50  
% 55.36/7.50  ------  iProver source info
% 55.36/7.50  
% 55.36/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.36/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.36/7.50  git: non_committed_changes: false
% 55.36/7.50  git: last_make_outside_of_git: false
% 55.36/7.50  
% 55.36/7.50  ------ 
% 55.36/7.50  ------ Parsing...
% 55.36/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.36/7.50  
% 55.36/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 55.36/7.50  
% 55.36/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.36/7.50  
% 55.36/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.36/7.50  ------ Proving...
% 55.36/7.50  ------ Problem Properties 
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  clauses                                 23
% 55.36/7.50  conjectures                             2
% 55.36/7.50  EPR                                     3
% 55.36/7.50  Horn                                    21
% 55.36/7.50  unary                                   11
% 55.36/7.50  binary                                  8
% 55.36/7.50  lits                                    41
% 55.36/7.50  lits eq                                 19
% 55.36/7.50  fd_pure                                 0
% 55.36/7.50  fd_pseudo                               0
% 55.36/7.50  fd_cond                                 1
% 55.36/7.50  fd_pseudo_cond                          1
% 55.36/7.50  AC symbols                              0
% 55.36/7.50  
% 55.36/7.50  ------ Input Options Time Limit: Unbounded
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  ------ 
% 55.36/7.50  Current options:
% 55.36/7.50  ------ 
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  ------ Proving...
% 55.36/7.50  
% 55.36/7.50  
% 55.36/7.50  % SZS status Theorem for theBenchmark.p
% 55.36/7.50  
% 55.36/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.36/7.50  
% 55.36/7.50  fof(f25,conjecture,(
% 55.36/7.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f26,negated_conjecture,(
% 55.36/7.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 55.36/7.50    inference(negated_conjecture,[],[f25])).
% 55.36/7.50  
% 55.36/7.50  fof(f37,plain,(
% 55.36/7.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 55.36/7.50    inference(ennf_transformation,[],[f26])).
% 55.36/7.50  
% 55.36/7.50  fof(f45,plain,(
% 55.36/7.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 55.36/7.50    introduced(choice_axiom,[])).
% 55.36/7.50  
% 55.36/7.50  fof(f46,plain,(
% 55.36/7.50    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 55.36/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f45])).
% 55.36/7.50  
% 55.36/7.50  fof(f77,plain,(
% 55.36/7.50    v1_relat_1(sK3)),
% 55.36/7.50    inference(cnf_transformation,[],[f46])).
% 55.36/7.50  
% 55.36/7.50  fof(f19,axiom,(
% 55.36/7.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f29,plain,(
% 55.36/7.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 55.36/7.50    inference(ennf_transformation,[],[f19])).
% 55.36/7.50  
% 55.36/7.50  fof(f40,plain,(
% 55.36/7.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 55.36/7.50    inference(nnf_transformation,[],[f29])).
% 55.36/7.50  
% 55.36/7.50  fof(f41,plain,(
% 55.36/7.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 55.36/7.50    inference(rectify,[],[f40])).
% 55.36/7.50  
% 55.36/7.50  fof(f43,plain,(
% 55.36/7.50    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 55.36/7.50    introduced(choice_axiom,[])).
% 55.36/7.50  
% 55.36/7.50  fof(f42,plain,(
% 55.36/7.50    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 55.36/7.50    introduced(choice_axiom,[])).
% 55.36/7.50  
% 55.36/7.50  fof(f44,plain,(
% 55.36/7.50    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 55.36/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f43,f42])).
% 55.36/7.50  
% 55.36/7.50  fof(f69,plain,(
% 55.36/7.50    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f44])).
% 55.36/7.50  
% 55.36/7.50  fof(f14,axiom,(
% 55.36/7.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f38,plain,(
% 55.36/7.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 55.36/7.50    inference(nnf_transformation,[],[f14])).
% 55.36/7.50  
% 55.36/7.50  fof(f61,plain,(
% 55.36/7.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f38])).
% 55.36/7.50  
% 55.36/7.50  fof(f7,axiom,(
% 55.36/7.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f53,plain,(
% 55.36/7.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f7])).
% 55.36/7.50  
% 55.36/7.50  fof(f8,axiom,(
% 55.36/7.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f54,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f8])).
% 55.36/7.50  
% 55.36/7.50  fof(f9,axiom,(
% 55.36/7.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f55,plain,(
% 55.36/7.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f9])).
% 55.36/7.50  
% 55.36/7.50  fof(f10,axiom,(
% 55.36/7.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f56,plain,(
% 55.36/7.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f10])).
% 55.36/7.50  
% 55.36/7.50  fof(f11,axiom,(
% 55.36/7.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f57,plain,(
% 55.36/7.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f11])).
% 55.36/7.50  
% 55.36/7.50  fof(f12,axiom,(
% 55.36/7.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f58,plain,(
% 55.36/7.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f12])).
% 55.36/7.50  
% 55.36/7.50  fof(f13,axiom,(
% 55.36/7.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f59,plain,(
% 55.36/7.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f13])).
% 55.36/7.50  
% 55.36/7.50  fof(f79,plain,(
% 55.36/7.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f58,f59])).
% 55.36/7.50  
% 55.36/7.50  fof(f80,plain,(
% 55.36/7.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f57,f79])).
% 55.36/7.50  
% 55.36/7.50  fof(f81,plain,(
% 55.36/7.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f56,f80])).
% 55.36/7.50  
% 55.36/7.50  fof(f82,plain,(
% 55.36/7.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f55,f81])).
% 55.36/7.50  
% 55.36/7.50  fof(f83,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f54,f82])).
% 55.36/7.50  
% 55.36/7.50  fof(f86,plain,(
% 55.36/7.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f53,f83])).
% 55.36/7.50  
% 55.36/7.50  fof(f89,plain,(
% 55.36/7.50    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f61,f86])).
% 55.36/7.50  
% 55.36/7.50  fof(f5,axiom,(
% 55.36/7.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f28,plain,(
% 55.36/7.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 55.36/7.50    inference(ennf_transformation,[],[f5])).
% 55.36/7.50  
% 55.36/7.50  fof(f51,plain,(
% 55.36/7.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f28])).
% 55.36/7.50  
% 55.36/7.50  fof(f17,axiom,(
% 55.36/7.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f39,plain,(
% 55.36/7.50    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 55.36/7.50    inference(nnf_transformation,[],[f17])).
% 55.36/7.50  
% 55.36/7.50  fof(f65,plain,(
% 55.36/7.50    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f39])).
% 55.36/7.50  
% 55.36/7.50  fof(f2,axiom,(
% 55.36/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f48,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.36/7.50    inference(cnf_transformation,[],[f2])).
% 55.36/7.50  
% 55.36/7.50  fof(f18,axiom,(
% 55.36/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f67,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.36/7.50    inference(cnf_transformation,[],[f18])).
% 55.36/7.50  
% 55.36/7.50  fof(f84,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 55.36/7.50    inference(definition_unfolding,[],[f67,f83])).
% 55.36/7.50  
% 55.36/7.50  fof(f85,plain,(
% 55.36/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.36/7.50    inference(definition_unfolding,[],[f48,f84])).
% 55.36/7.50  
% 55.36/7.50  fof(f95,plain,(
% 55.36/7.50    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 55.36/7.50    inference(definition_unfolding,[],[f65,f85,f86,f86,f86])).
% 55.36/7.50  
% 55.36/7.50  fof(f97,plain,(
% 55.36/7.50    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 55.36/7.50    inference(equality_resolution,[],[f95])).
% 55.36/7.50  
% 55.36/7.50  fof(f1,axiom,(
% 55.36/7.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f27,plain,(
% 55.36/7.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 55.36/7.50    inference(rectify,[],[f1])).
% 55.36/7.50  
% 55.36/7.50  fof(f47,plain,(
% 55.36/7.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 55.36/7.50    inference(cnf_transformation,[],[f27])).
% 55.36/7.50  
% 55.36/7.50  fof(f87,plain,(
% 55.36/7.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 55.36/7.50    inference(definition_unfolding,[],[f47,f84])).
% 55.36/7.50  
% 55.36/7.50  fof(f6,axiom,(
% 55.36/7.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f52,plain,(
% 55.36/7.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.36/7.50    inference(cnf_transformation,[],[f6])).
% 55.36/7.50  
% 55.36/7.50  fof(f20,axiom,(
% 55.36/7.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f30,plain,(
% 55.36/7.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 55.36/7.50    inference(ennf_transformation,[],[f20])).
% 55.36/7.50  
% 55.36/7.50  fof(f31,plain,(
% 55.36/7.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 55.36/7.50    inference(flattening,[],[f30])).
% 55.36/7.50  
% 55.36/7.50  fof(f71,plain,(
% 55.36/7.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.36/7.50    inference(cnf_transformation,[],[f31])).
% 55.36/7.50  
% 55.36/7.50  fof(f21,axiom,(
% 55.36/7.50    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 55.36/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.50  
% 55.36/7.50  fof(f32,plain,(
% 55.36/7.50    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 55.36/7.51    inference(ennf_transformation,[],[f21])).
% 55.36/7.51  
% 55.36/7.51  fof(f72,plain,(
% 55.36/7.51    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 55.36/7.51    inference(cnf_transformation,[],[f32])).
% 55.36/7.51  
% 55.36/7.51  fof(f96,plain,(
% 55.36/7.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 55.36/7.51    inference(definition_unfolding,[],[f72,f84])).
% 55.36/7.51  
% 55.36/7.51  fof(f24,axiom,(
% 55.36/7.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f76,plain,(
% 55.36/7.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 55.36/7.51    inference(cnf_transformation,[],[f24])).
% 55.36/7.51  
% 55.36/7.51  fof(f22,axiom,(
% 55.36/7.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f33,plain,(
% 55.36/7.51    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.36/7.51    inference(ennf_transformation,[],[f22])).
% 55.36/7.51  
% 55.36/7.51  fof(f34,plain,(
% 55.36/7.51    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.36/7.51    inference(flattening,[],[f33])).
% 55.36/7.51  
% 55.36/7.51  fof(f73,plain,(
% 55.36/7.51    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.36/7.51    inference(cnf_transformation,[],[f34])).
% 55.36/7.51  
% 55.36/7.51  fof(f75,plain,(
% 55.36/7.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 55.36/7.51    inference(cnf_transformation,[],[f24])).
% 55.36/7.51  
% 55.36/7.51  fof(f4,axiom,(
% 55.36/7.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f50,plain,(
% 55.36/7.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 55.36/7.51    inference(cnf_transformation,[],[f4])).
% 55.36/7.51  
% 55.36/7.51  fof(f3,axiom,(
% 55.36/7.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f49,plain,(
% 55.36/7.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.36/7.51    inference(cnf_transformation,[],[f3])).
% 55.36/7.51  
% 55.36/7.51  fof(f88,plain,(
% 55.36/7.51    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 55.36/7.51    inference(definition_unfolding,[],[f49,f84])).
% 55.36/7.51  
% 55.36/7.51  fof(f15,axiom,(
% 55.36/7.51    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f62,plain,(
% 55.36/7.51    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 55.36/7.51    inference(cnf_transformation,[],[f15])).
% 55.36/7.51  
% 55.36/7.51  fof(f91,plain,(
% 55.36/7.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 55.36/7.51    inference(definition_unfolding,[],[f62,f84,f84,f84])).
% 55.36/7.51  
% 55.36/7.51  fof(f16,axiom,(
% 55.36/7.51    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f63,plain,(
% 55.36/7.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 55.36/7.51    inference(cnf_transformation,[],[f16])).
% 55.36/7.51  
% 55.36/7.51  fof(f93,plain,(
% 55.36/7.51    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2)) )),
% 55.36/7.51    inference(definition_unfolding,[],[f63,f85,f85])).
% 55.36/7.51  
% 55.36/7.51  fof(f23,axiom,(
% 55.36/7.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 55.36/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.36/7.51  
% 55.36/7.51  fof(f35,plain,(
% 55.36/7.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.36/7.51    inference(ennf_transformation,[],[f23])).
% 55.36/7.51  
% 55.36/7.51  fof(f36,plain,(
% 55.36/7.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.36/7.51    inference(flattening,[],[f35])).
% 55.36/7.51  
% 55.36/7.51  fof(f74,plain,(
% 55.36/7.51    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.36/7.51    inference(cnf_transformation,[],[f36])).
% 55.36/7.51  
% 55.36/7.51  fof(f64,plain,(
% 55.36/7.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 55.36/7.51    inference(cnf_transformation,[],[f16])).
% 55.36/7.51  
% 55.36/7.51  fof(f92,plain,(
% 55.36/7.51    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 55.36/7.51    inference(definition_unfolding,[],[f64,f85,f85])).
% 55.36/7.51  
% 55.36/7.51  fof(f66,plain,(
% 55.36/7.51    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 55.36/7.51    inference(cnf_transformation,[],[f39])).
% 55.36/7.51  
% 55.36/7.51  fof(f94,plain,(
% 55.36/7.51    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 55.36/7.51    inference(definition_unfolding,[],[f66,f85,f86,f86,f86])).
% 55.36/7.51  
% 55.36/7.51  fof(f78,plain,(
% 55.36/7.51    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 55.36/7.51    inference(cnf_transformation,[],[f46])).
% 55.36/7.51  
% 55.36/7.51  cnf(c_22,negated_conjecture,
% 55.36/7.51      ( v1_relat_1(sK3) ),
% 55.36/7.51      inference(cnf_transformation,[],[f77]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_545,plain,
% 55.36/7.51      ( v1_relat_1(sK3) = iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_13,plain,
% 55.36/7.51      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 55.36/7.51      inference(cnf_transformation,[],[f69]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_551,plain,
% 55.36/7.51      ( r2_hidden(sK0(X0),X0) = iProver_top
% 55.36/7.51      | v1_relat_1(X0) = iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_5,plain,
% 55.36/7.51      ( ~ r2_hidden(X0,X1)
% 55.36/7.51      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 55.36/7.51      inference(cnf_transformation,[],[f89]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_554,plain,
% 55.36/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.36/7.51      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_3,plain,
% 55.36/7.51      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f51]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_555,plain,
% 55.36/7.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1165,plain,
% 55.36/7.51      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 55.36/7.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_554,c_555]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_11,plain,
% 55.36/7.51      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 55.36/7.51      inference(cnf_transformation,[],[f97]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_0,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f87]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_4,plain,
% 55.36/7.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f52]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_641,plain,
% 55.36/7.51      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_11,c_0,c_4]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1270,plain,
% 55.36/7.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(global_propositional_subsumption,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_1165,c_641]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1406,plain,
% 55.36/7.51      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_551,c_1270]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_15,plain,
% 55.36/7.51      ( ~ v1_relat_1(X0)
% 55.36/7.51      | ~ v1_relat_1(X1)
% 55.36/7.51      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 55.36/7.51      inference(cnf_transformation,[],[f71]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_549,plain,
% 55.36/7.51      ( v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(X1) != iProver_top
% 55.36/7.51      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_16,plain,
% 55.36/7.51      ( ~ v1_relat_1(X0)
% 55.36/7.51      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f96]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_548,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1280,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(X1) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_549,c_548]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2954,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_1406,c_1280]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_51127,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_2954]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_19,plain,
% 55.36/7.51      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f76]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_17,plain,
% 55.36/7.51      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 55.36/7.51      | ~ v1_relat_1(X0)
% 55.36/7.51      | ~ v1_relat_1(X1)
% 55.36/7.51      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 55.36/7.51      inference(cnf_transformation,[],[f73]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_547,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 55.36/7.51      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(X1) != iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1377,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 55.36/7.51      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_19,c_547]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_20,plain,
% 55.36/7.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f75]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1391,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.36/7.51      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_1377,c_20]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1486,plain,
% 55.36/7.51      ( v1_relat_1(X0) != iProver_top
% 55.36/7.51      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.36/7.51      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 55.36/7.51      inference(global_propositional_subsumption,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_1391,c_1406]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1487,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.36/7.51      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(renaming,[status(thm)],[c_1486]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2,plain,
% 55.36/7.51      ( r1_tarski(k1_xboole_0,X0) ),
% 55.36/7.51      inference(cnf_transformation,[],[f50]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_556,plain,
% 55.36/7.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1493,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(forward_subsumption_resolution,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_1487,c_556]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1498,plain,
% 55.36/7.51      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_1493]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_51132,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_51127,c_1498]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.36/7.51      inference(cnf_transformation,[],[f88]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1281,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = sK3 ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_548]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_7,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
% 55.36/7.51      inference(cnf_transformation,[],[f91]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_9,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.36/7.51      inference(cnf_transformation,[],[f93]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_633,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_7,c_9]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_635,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_633,c_0]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2217,plain,
% 55.36/7.51      ( k2_zfmisc_1(k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),X0) = k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_1281,c_635]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2219,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(k5_xboole_0(sK3,sK3),X0) ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_2217,c_1281]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2220,plain,
% 55.36/7.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_2219,c_4]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_51133,plain,
% 55.36/7.51      ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_51132,c_1,c_2220]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2066,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_1280]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2953,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_1406,c_2066]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_18,plain,
% 55.36/7.51      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 55.36/7.51      | ~ v1_relat_1(X0)
% 55.36/7.51      | ~ v1_relat_1(X1)
% 55.36/7.51      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 55.36/7.51      inference(cnf_transformation,[],[f74]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_546,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 55.36/7.51      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X1) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_774,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 55.36/7.51      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_20,c_546]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_788,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.36/7.51      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_774,c_19]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1461,plain,
% 55.36/7.51      ( v1_relat_1(X0) != iProver_top
% 55.36/7.51      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.36/7.51      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.36/7.51      inference(global_propositional_subsumption,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_788,c_1406]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1462,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.36/7.51      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(renaming,[status(thm)],[c_1461]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1468,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(forward_subsumption_resolution,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_1462,c_556]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_1473,plain,
% 55.36/7.51      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_1468]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2970,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_2953,c_1473]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2516,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1)))))) = k5_relat_1(sK3,k5_relat_1(X0,X1))
% 55.36/7.51      | v1_relat_1(X0) != iProver_top
% 55.36/7.51      | v1_relat_1(X1) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_549,c_2066]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2728,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0)))))) = k5_relat_1(sK3,k5_relat_1(sK3,X0))
% 55.36/7.51      | v1_relat_1(X0) != iProver_top ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_2516]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2777,plain,
% 55.36/7.51      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_545,c_2728]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_8,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.36/7.51      inference(cnf_transformation,[],[f92]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_632,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_7,c_8]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_638,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_632,c_0]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2990,plain,
% 55.36/7.51      ( k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
% 55.36/7.51      inference(superposition,[status(thm)],[c_2777,c_638]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2992,plain,
% 55.36/7.51      ( k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
% 55.36/7.51      inference(light_normalisation,[status(thm)],[c_2990,c_2777]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_2993,plain,
% 55.36/7.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_2992,c_4]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_3392,plain,
% 55.36/7.51      ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 55.36/7.51      inference(demodulation,[status(thm)],[c_2970,c_1,c_2993]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_185,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_763,plain,
% 55.36/7.51      ( k5_relat_1(sK3,k1_xboole_0) != X0
% 55.36/7.51      | k1_xboole_0 != X0
% 55.36/7.51      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_185]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_764,plain,
% 55.36/7.51      ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 55.36/7.51      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
% 55.36/7.51      | k1_xboole_0 != k1_xboole_0 ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_763]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_705,plain,
% 55.36/7.51      ( k5_relat_1(k1_xboole_0,sK3) != X0
% 55.36/7.51      | k1_xboole_0 != X0
% 55.36/7.51      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_185]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_706,plain,
% 55.36/7.51      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 55.36/7.51      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
% 55.36/7.51      | k1_xboole_0 != k1_xboole_0 ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_705]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_10,plain,
% 55.36/7.51      ( X0 = X1
% 55.36/7.51      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 55.36/7.51      inference(cnf_transformation,[],[f94]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_46,plain,
% 55.36/7.51      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 55.36/7.51      | k1_xboole_0 = k1_xboole_0 ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_10]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_45,plain,
% 55.36/7.51      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 55.36/7.51      inference(instantiation,[status(thm)],[c_11]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(c_21,negated_conjecture,
% 55.36/7.51      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 55.36/7.51      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 55.36/7.51      inference(cnf_transformation,[],[f78]) ).
% 55.36/7.51  
% 55.36/7.51  cnf(contradiction,plain,
% 55.36/7.51      ( $false ),
% 55.36/7.51      inference(minisat,
% 55.36/7.51                [status(thm)],
% 55.36/7.51                [c_51133,c_3392,c_764,c_706,c_46,c_45,c_21]) ).
% 55.36/7.51  
% 55.36/7.51  
% 55.36/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.36/7.51  
% 55.36/7.51  ------                               Statistics
% 55.36/7.51  
% 55.36/7.51  ------ Selected
% 55.36/7.51  
% 55.36/7.51  total_time:                             6.973
% 55.36/7.51  
%------------------------------------------------------------------------------
