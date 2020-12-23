%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:18 EST 2020

% Result     : Theorem 55.07s
% Output     : CNFRefutation 55.07s
% Verified   : 
% Statistics : Number of formulae       :  168 (1531 expanded)
%              Number of clauses        :   76 ( 178 expanded)
%              Number of leaves         :   29 ( 466 expanded)
%              Depth                    :   21
%              Number of atoms          :  328 (2102 expanded)
%              Number of equality atoms :  228 (1691 expanded)
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

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f44])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f83])).

fof(f93,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f63,f84,f85,f85,f85])).

fof(f96,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f85])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f83])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f60,f83,f83,f83])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) ),
    inference(definition_unfolding,[],[f61,f84,f84])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f62,f84,f84])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f64,f84,f85,f85,f85])).

fof(f77,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_545,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_551,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_554,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_555,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1165,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_555])).

cnf(c_10,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_641,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_3,c_11])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_549,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f95])).

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

cnf(c_51245,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_545,c_2954])).

cnf(c_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f74])).

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

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_556,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1493,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1487,c_556])).

cnf(c_1498,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_545,c_1493])).

cnf(c_51250,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_51245,c_1498])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1281,plain,
    ( k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = sK3 ),
    inference(superposition,[status(thm)],[c_545,c_548])).

cnf(c_6,plain,
    ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_633,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(demodulation,[status(thm)],[c_6,c_8])).

cnf(c_635,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
    inference(demodulation,[status(thm)],[c_633,c_11])).

cnf(c_2217,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),X0) = k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1281,c_635])).

cnf(c_2219,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(k5_xboole_0(sK3,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_2217,c_1281])).

cnf(c_2220,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2219,c_3])).

cnf(c_51251,plain,
    ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_51250,c_0,c_2220])).

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
    inference(cnf_transformation,[],[f73])).

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

cnf(c_7,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_632,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_6,c_7])).

cnf(c_638,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_632,c_11])).

cnf(c_2990,plain,
    ( k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
    inference(superposition,[status(thm)],[c_2777,c_638])).

cnf(c_2992,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_2990,c_2777])).

cnf(c_2993,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2992,c_3])).

cnf(c_3389,plain,
    ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2970,c_0,c_2993])).

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

cnf(c_9,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_47,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_46,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51251,c_3389,c_764,c_706,c_47,c_46,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 55.07/7.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.07/7.53  
% 55.07/7.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.07/7.53  
% 55.07/7.53  ------  iProver source info
% 55.07/7.53  
% 55.07/7.53  git: date: 2020-06-30 10:37:57 +0100
% 55.07/7.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.07/7.53  git: non_committed_changes: false
% 55.07/7.53  git: last_make_outside_of_git: false
% 55.07/7.53  
% 55.07/7.53  ------ 
% 55.07/7.53  ------ Parsing...
% 55.07/7.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.07/7.53  
% 55.07/7.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 55.07/7.53  
% 55.07/7.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.07/7.53  
% 55.07/7.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.07/7.53  ------ Proving...
% 55.07/7.53  ------ Problem Properties 
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  clauses                                 23
% 55.07/7.53  conjectures                             2
% 55.07/7.53  EPR                                     3
% 55.07/7.53  Horn                                    21
% 55.07/7.53  unary                                   11
% 55.07/7.53  binary                                  8
% 55.07/7.53  lits                                    41
% 55.07/7.53  lits eq                                 19
% 55.07/7.53  fd_pure                                 0
% 55.07/7.53  fd_pseudo                               0
% 55.07/7.53  fd_cond                                 1
% 55.07/7.53  fd_pseudo_cond                          1
% 55.07/7.53  AC symbols                              0
% 55.07/7.53  
% 55.07/7.53  ------ Input Options Time Limit: Unbounded
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  ------ 
% 55.07/7.53  Current options:
% 55.07/7.53  ------ 
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  ------ Proving...
% 55.07/7.53  
% 55.07/7.53  
% 55.07/7.53  % SZS status Theorem for theBenchmark.p
% 55.07/7.53  
% 55.07/7.53  % SZS output start CNFRefutation for theBenchmark.p
% 55.07/7.53  
% 55.07/7.53  fof(f25,conjecture,(
% 55.07/7.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 55.07/7.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.53  
% 55.07/7.53  fof(f26,negated_conjecture,(
% 55.07/7.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 55.07/7.53    inference(negated_conjecture,[],[f25])).
% 55.07/7.53  
% 55.07/7.53  fof(f36,plain,(
% 55.07/7.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 55.07/7.53    inference(ennf_transformation,[],[f26])).
% 55.07/7.53  
% 55.07/7.53  fof(f44,plain,(
% 55.07/7.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3))),
% 55.07/7.54    introduced(choice_axiom,[])).
% 55.07/7.54  
% 55.07/7.54  fof(f45,plain,(
% 55.07/7.54    (k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)) & v1_relat_1(sK3)),
% 55.07/7.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f44])).
% 55.07/7.54  
% 55.07/7.54  fof(f76,plain,(
% 55.07/7.54    v1_relat_1(sK3)),
% 55.07/7.54    inference(cnf_transformation,[],[f45])).
% 55.07/7.54  
% 55.07/7.54  fof(f19,axiom,(
% 55.07/7.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f28,plain,(
% 55.07/7.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 55.07/7.54    inference(ennf_transformation,[],[f19])).
% 55.07/7.54  
% 55.07/7.54  fof(f39,plain,(
% 55.07/7.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 55.07/7.54    inference(nnf_transformation,[],[f28])).
% 55.07/7.54  
% 55.07/7.54  fof(f40,plain,(
% 55.07/7.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 55.07/7.54    inference(rectify,[],[f39])).
% 55.07/7.54  
% 55.07/7.54  fof(f42,plain,(
% 55.07/7.54    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 55.07/7.54    introduced(choice_axiom,[])).
% 55.07/7.54  
% 55.07/7.54  fof(f41,plain,(
% 55.07/7.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 55.07/7.54    introduced(choice_axiom,[])).
% 55.07/7.54  
% 55.07/7.54  fof(f43,plain,(
% 55.07/7.54    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 55.07/7.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42,f41])).
% 55.07/7.54  
% 55.07/7.54  fof(f68,plain,(
% 55.07/7.54    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f43])).
% 55.07/7.54  
% 55.07/7.54  fof(f13,axiom,(
% 55.07/7.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f37,plain,(
% 55.07/7.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 55.07/7.54    inference(nnf_transformation,[],[f13])).
% 55.07/7.54  
% 55.07/7.54  fof(f59,plain,(
% 55.07/7.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f37])).
% 55.07/7.54  
% 55.07/7.54  fof(f6,axiom,(
% 55.07/7.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f51,plain,(
% 55.07/7.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f6])).
% 55.07/7.54  
% 55.07/7.54  fof(f7,axiom,(
% 55.07/7.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f52,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f7])).
% 55.07/7.54  
% 55.07/7.54  fof(f8,axiom,(
% 55.07/7.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f53,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f8])).
% 55.07/7.54  
% 55.07/7.54  fof(f9,axiom,(
% 55.07/7.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f54,plain,(
% 55.07/7.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f9])).
% 55.07/7.54  
% 55.07/7.54  fof(f10,axiom,(
% 55.07/7.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f55,plain,(
% 55.07/7.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f10])).
% 55.07/7.54  
% 55.07/7.54  fof(f11,axiom,(
% 55.07/7.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f56,plain,(
% 55.07/7.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f11])).
% 55.07/7.54  
% 55.07/7.54  fof(f12,axiom,(
% 55.07/7.54    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f57,plain,(
% 55.07/7.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f12])).
% 55.07/7.54  
% 55.07/7.54  fof(f78,plain,(
% 55.07/7.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f56,f57])).
% 55.07/7.54  
% 55.07/7.54  fof(f79,plain,(
% 55.07/7.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f55,f78])).
% 55.07/7.54  
% 55.07/7.54  fof(f80,plain,(
% 55.07/7.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f54,f79])).
% 55.07/7.54  
% 55.07/7.54  fof(f81,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f53,f80])).
% 55.07/7.54  
% 55.07/7.54  fof(f82,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f52,f81])).
% 55.07/7.54  
% 55.07/7.54  fof(f85,plain,(
% 55.07/7.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f51,f82])).
% 55.07/7.54  
% 55.07/7.54  fof(f87,plain,(
% 55.07/7.54    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f59,f85])).
% 55.07/7.54  
% 55.07/7.54  fof(f4,axiom,(
% 55.07/7.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f27,plain,(
% 55.07/7.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 55.07/7.54    inference(ennf_transformation,[],[f4])).
% 55.07/7.54  
% 55.07/7.54  fof(f49,plain,(
% 55.07/7.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f27])).
% 55.07/7.54  
% 55.07/7.54  fof(f16,axiom,(
% 55.07/7.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f38,plain,(
% 55.07/7.54    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 55.07/7.54    inference(nnf_transformation,[],[f16])).
% 55.07/7.54  
% 55.07/7.54  fof(f63,plain,(
% 55.07/7.54    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f38])).
% 55.07/7.54  
% 55.07/7.54  fof(f1,axiom,(
% 55.07/7.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f46,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.07/7.54    inference(cnf_transformation,[],[f1])).
% 55.07/7.54  
% 55.07/7.54  fof(f18,axiom,(
% 55.07/7.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f66,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.07/7.54    inference(cnf_transformation,[],[f18])).
% 55.07/7.54  
% 55.07/7.54  fof(f83,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 55.07/7.54    inference(definition_unfolding,[],[f66,f82])).
% 55.07/7.54  
% 55.07/7.54  fof(f84,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.07/7.54    inference(definition_unfolding,[],[f46,f83])).
% 55.07/7.54  
% 55.07/7.54  fof(f93,plain,(
% 55.07/7.54    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f63,f84,f85,f85,f85])).
% 55.07/7.54  
% 55.07/7.54  fof(f96,plain,(
% 55.07/7.54    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 55.07/7.54    inference(equality_resolution,[],[f93])).
% 55.07/7.54  
% 55.07/7.54  fof(f5,axiom,(
% 55.07/7.54    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f50,plain,(
% 55.07/7.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.07/7.54    inference(cnf_transformation,[],[f5])).
% 55.07/7.54  
% 55.07/7.54  fof(f17,axiom,(
% 55.07/7.54    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f65,plain,(
% 55.07/7.54    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 55.07/7.54    inference(cnf_transformation,[],[f17])).
% 55.07/7.54  
% 55.07/7.54  fof(f94,plain,(
% 55.07/7.54    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 55.07/7.54    inference(definition_unfolding,[],[f65,f85])).
% 55.07/7.54  
% 55.07/7.54  fof(f20,axiom,(
% 55.07/7.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f29,plain,(
% 55.07/7.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 55.07/7.54    inference(ennf_transformation,[],[f20])).
% 55.07/7.54  
% 55.07/7.54  fof(f30,plain,(
% 55.07/7.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 55.07/7.54    inference(flattening,[],[f29])).
% 55.07/7.54  
% 55.07/7.54  fof(f70,plain,(
% 55.07/7.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f30])).
% 55.07/7.54  
% 55.07/7.54  fof(f21,axiom,(
% 55.07/7.54    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f31,plain,(
% 55.07/7.54    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 55.07/7.54    inference(ennf_transformation,[],[f21])).
% 55.07/7.54  
% 55.07/7.54  fof(f71,plain,(
% 55.07/7.54    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f31])).
% 55.07/7.54  
% 55.07/7.54  fof(f95,plain,(
% 55.07/7.54    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f71,f83])).
% 55.07/7.54  
% 55.07/7.54  fof(f24,axiom,(
% 55.07/7.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f75,plain,(
% 55.07/7.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 55.07/7.54    inference(cnf_transformation,[],[f24])).
% 55.07/7.54  
% 55.07/7.54  fof(f22,axiom,(
% 55.07/7.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f32,plain,(
% 55.07/7.54    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.07/7.54    inference(ennf_transformation,[],[f22])).
% 55.07/7.54  
% 55.07/7.54  fof(f33,plain,(
% 55.07/7.54    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.07/7.54    inference(flattening,[],[f32])).
% 55.07/7.54  
% 55.07/7.54  fof(f72,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f33])).
% 55.07/7.54  
% 55.07/7.54  fof(f74,plain,(
% 55.07/7.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 55.07/7.54    inference(cnf_transformation,[],[f24])).
% 55.07/7.54  
% 55.07/7.54  fof(f3,axiom,(
% 55.07/7.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f48,plain,(
% 55.07/7.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f3])).
% 55.07/7.54  
% 55.07/7.54  fof(f2,axiom,(
% 55.07/7.54    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f47,plain,(
% 55.07/7.54    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.07/7.54    inference(cnf_transformation,[],[f2])).
% 55.07/7.54  
% 55.07/7.54  fof(f86,plain,(
% 55.07/7.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 55.07/7.54    inference(definition_unfolding,[],[f47,f83])).
% 55.07/7.54  
% 55.07/7.54  fof(f14,axiom,(
% 55.07/7.54    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f60,plain,(
% 55.07/7.54    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 55.07/7.54    inference(cnf_transformation,[],[f14])).
% 55.07/7.54  
% 55.07/7.54  fof(f89,plain,(
% 55.07/7.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 55.07/7.54    inference(definition_unfolding,[],[f60,f83,f83,f83])).
% 55.07/7.54  
% 55.07/7.54  fof(f15,axiom,(
% 55.07/7.54    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f61,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f15])).
% 55.07/7.54  
% 55.07/7.54  fof(f91,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2)) )),
% 55.07/7.54    inference(definition_unfolding,[],[f61,f84,f84])).
% 55.07/7.54  
% 55.07/7.54  fof(f23,axiom,(
% 55.07/7.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 55.07/7.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.07/7.54  
% 55.07/7.54  fof(f34,plain,(
% 55.07/7.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.07/7.54    inference(ennf_transformation,[],[f23])).
% 55.07/7.54  
% 55.07/7.54  fof(f35,plain,(
% 55.07/7.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.07/7.54    inference(flattening,[],[f34])).
% 55.07/7.54  
% 55.07/7.54  fof(f73,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.07/7.54    inference(cnf_transformation,[],[f35])).
% 55.07/7.54  
% 55.07/7.54  fof(f62,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 55.07/7.54    inference(cnf_transformation,[],[f15])).
% 55.07/7.54  
% 55.07/7.54  fof(f90,plain,(
% 55.07/7.54    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 55.07/7.54    inference(definition_unfolding,[],[f62,f84,f84])).
% 55.07/7.54  
% 55.07/7.54  fof(f64,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 55.07/7.54    inference(cnf_transformation,[],[f38])).
% 55.07/7.54  
% 55.07/7.54  fof(f92,plain,(
% 55.07/7.54    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 55.07/7.54    inference(definition_unfolding,[],[f64,f84,f85,f85,f85])).
% 55.07/7.54  
% 55.07/7.54  fof(f77,plain,(
% 55.07/7.54    k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)),
% 55.07/7.54    inference(cnf_transformation,[],[f45])).
% 55.07/7.54  
% 55.07/7.54  cnf(c_22,negated_conjecture,
% 55.07/7.54      ( v1_relat_1(sK3) ),
% 55.07/7.54      inference(cnf_transformation,[],[f76]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_545,plain,
% 55.07/7.54      ( v1_relat_1(sK3) = iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_13,plain,
% 55.07/7.54      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 55.07/7.54      inference(cnf_transformation,[],[f68]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_551,plain,
% 55.07/7.54      ( r2_hidden(sK0(X0),X0) = iProver_top
% 55.07/7.54      | v1_relat_1(X0) = iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_4,plain,
% 55.07/7.54      ( ~ r2_hidden(X0,X1)
% 55.07/7.54      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 55.07/7.54      inference(cnf_transformation,[],[f87]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_554,plain,
% 55.07/7.54      ( r2_hidden(X0,X1) != iProver_top
% 55.07/7.54      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2,plain,
% 55.07/7.54      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f49]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_555,plain,
% 55.07/7.54      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1165,plain,
% 55.07/7.54      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 55.07/7.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_554,c_555]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_10,plain,
% 55.07/7.54      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 55.07/7.54      inference(cnf_transformation,[],[f96]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_3,plain,
% 55.07/7.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f50]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_11,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f94]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_641,plain,
% 55.07/7.54      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_10,c_3,c_11]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1270,plain,
% 55.07/7.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(global_propositional_subsumption,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_1165,c_641]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1406,plain,
% 55.07/7.54      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_551,c_1270]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_15,plain,
% 55.07/7.54      ( ~ v1_relat_1(X0)
% 55.07/7.54      | ~ v1_relat_1(X1)
% 55.07/7.54      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 55.07/7.54      inference(cnf_transformation,[],[f70]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_549,plain,
% 55.07/7.54      ( v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(X1) != iProver_top
% 55.07/7.54      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_16,plain,
% 55.07/7.54      ( ~ v1_relat_1(X0)
% 55.07/7.54      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f95]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_548,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1280,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(X1) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_549,c_548]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2954,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_1406,c_1280]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_51245,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_2954]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_19,plain,
% 55.07/7.54      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f75]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_17,plain,
% 55.07/7.54      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 55.07/7.54      | ~ v1_relat_1(X0)
% 55.07/7.54      | ~ v1_relat_1(X1)
% 55.07/7.54      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 55.07/7.54      inference(cnf_transformation,[],[f72]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_547,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 55.07/7.54      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(X1) != iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1377,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 55.07/7.54      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_19,c_547]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_20,plain,
% 55.07/7.54      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f74]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1391,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.07/7.54      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_1377,c_20]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1486,plain,
% 55.07/7.54      ( v1_relat_1(X0) != iProver_top
% 55.07/7.54      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.07/7.54      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 55.07/7.54      inference(global_propositional_subsumption,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_1391,c_1406]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1487,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.07/7.54      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(renaming,[status(thm)],[c_1486]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1,plain,
% 55.07/7.54      ( r1_tarski(k1_xboole_0,X0) ),
% 55.07/7.54      inference(cnf_transformation,[],[f48]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_556,plain,
% 55.07/7.54      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1493,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(forward_subsumption_resolution,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_1487,c_556]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1498,plain,
% 55.07/7.54      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_1493]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_51250,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK3))))) = k5_relat_1(k1_xboole_0,sK3) ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_51245,c_1498]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_0,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.07/7.54      inference(cnf_transformation,[],[f86]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1281,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = sK3 ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_548]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_6,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
% 55.07/7.54      inference(cnf_transformation,[],[f89]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_8,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.07/7.54      inference(cnf_transformation,[],[f91]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_633,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_6,c_8]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_635,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))),X1) ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_633,c_11]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2217,plain,
% 55.07/7.54      ( k2_zfmisc_1(k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),X0) = k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_1281,c_635]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2219,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(sK3,X0),k2_zfmisc_1(sK3,X0)) = k2_zfmisc_1(k5_xboole_0(sK3,sK3),X0) ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_2217,c_1281]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2220,plain,
% 55.07/7.54      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_2219,c_3]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_51251,plain,
% 55.07/7.54      ( k5_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_51250,c_0,c_2220]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2066,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k5_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,X0)),k2_relat_1(k5_relat_1(sK3,X0))))) = k5_relat_1(sK3,X0)
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_1280]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2953,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k5_relat_1(sK3,k1_xboole_0))))) = k5_relat_1(sK3,k1_xboole_0) ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_1406,c_2066]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_18,plain,
% 55.07/7.54      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 55.07/7.54      | ~ v1_relat_1(X0)
% 55.07/7.54      | ~ v1_relat_1(X1)
% 55.07/7.54      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 55.07/7.54      inference(cnf_transformation,[],[f73]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_546,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 55.07/7.54      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X1) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_774,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 55.07/7.54      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_20,c_546]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_788,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.07/7.54      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_774,c_19]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1461,plain,
% 55.07/7.54      ( v1_relat_1(X0) != iProver_top
% 55.07/7.54      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.07/7.54      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.07/7.54      inference(global_propositional_subsumption,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_788,c_1406]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1462,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.07/7.54      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(renaming,[status(thm)],[c_1461]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1468,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(forward_subsumption_resolution,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_1462,c_556]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_1473,plain,
% 55.07/7.54      ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_1468]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2970,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK3,k1_xboole_0) ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_2953,c_1473]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2516,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k5_relat_1(sK3,k5_relat_1(X0,X1)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X1)))))) = k5_relat_1(sK3,k5_relat_1(X0,X1))
% 55.07/7.54      | v1_relat_1(X0) != iProver_top
% 55.07/7.54      | v1_relat_1(X1) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_549,c_2066]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2728,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k5_relat_1(sK3,k5_relat_1(sK3,X0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X0)))))) = k5_relat_1(sK3,k5_relat_1(sK3,X0))
% 55.07/7.54      | v1_relat_1(X0) != iProver_top ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_2516]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2777,plain,
% 55.07/7.54      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_545,c_2728]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_7,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.07/7.54      inference(cnf_transformation,[],[f90]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_632,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_6,c_7]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_638,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_632,c_11]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2990,plain,
% 55.07/7.54      ( k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k1_setfam_1(k6_enumset1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))))))) = k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
% 55.07/7.54      inference(superposition,[status(thm)],[c_2777,c_638]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2992,plain,
% 55.07/7.54      ( k5_xboole_0(k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3))),k2_zfmisc_1(X0,k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k5_relat_1(sK3,sK3)))) ),
% 55.07/7.54      inference(light_normalisation,[status(thm)],[c_2990,c_2777]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_2993,plain,
% 55.07/7.54      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_2992,c_3]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_3389,plain,
% 55.07/7.54      ( k5_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 55.07/7.54      inference(demodulation,[status(thm)],[c_2970,c_0,c_2993]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_185,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_763,plain,
% 55.07/7.54      ( k5_relat_1(sK3,k1_xboole_0) != X0
% 55.07/7.54      | k1_xboole_0 != X0
% 55.07/7.54      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_185]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_764,plain,
% 55.07/7.54      ( k5_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 55.07/7.54      | k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
% 55.07/7.54      | k1_xboole_0 != k1_xboole_0 ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_763]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_705,plain,
% 55.07/7.54      ( k5_relat_1(k1_xboole_0,sK3) != X0
% 55.07/7.54      | k1_xboole_0 != X0
% 55.07/7.54      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_185]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_706,plain,
% 55.07/7.54      ( k5_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 55.07/7.54      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
% 55.07/7.54      | k1_xboole_0 != k1_xboole_0 ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_705]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_9,plain,
% 55.07/7.54      ( X0 = X1
% 55.07/7.54      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 55.07/7.54      inference(cnf_transformation,[],[f92]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_47,plain,
% 55.07/7.54      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 55.07/7.54      | k1_xboole_0 = k1_xboole_0 ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_9]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_46,plain,
% 55.07/7.54      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 55.07/7.54      inference(instantiation,[status(thm)],[c_10]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(c_21,negated_conjecture,
% 55.07/7.54      ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
% 55.07/7.54      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
% 55.07/7.54      inference(cnf_transformation,[],[f77]) ).
% 55.07/7.54  
% 55.07/7.54  cnf(contradiction,plain,
% 55.07/7.54      ( $false ),
% 55.07/7.54      inference(minisat,
% 55.07/7.54                [status(thm)],
% 55.07/7.54                [c_51251,c_3389,c_764,c_706,c_47,c_46,c_21]) ).
% 55.07/7.54  
% 55.07/7.54  
% 55.07/7.54  % SZS output end CNFRefutation for theBenchmark.p
% 55.07/7.54  
% 55.07/7.54  ------                               Statistics
% 55.07/7.54  
% 55.07/7.54  ------ Selected
% 55.07/7.54  
% 55.07/7.54  total_time:                             6.676
% 55.07/7.54  
%------------------------------------------------------------------------------
