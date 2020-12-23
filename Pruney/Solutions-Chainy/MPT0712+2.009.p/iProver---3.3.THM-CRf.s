%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:46 EST 2020

% Result     : Theorem 11.08s
% Output     : CNFRefutation 11.08s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 368 expanded)
%              Number of clauses        :   88 ( 126 expanded)
%              Number of leaves         :   21 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  418 ( 889 expanded)
%              Number of equality atoms :  124 ( 310 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f40])).

fof(f67,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f73,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f67,f70,f70])).

fof(f65,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f64,f69,f69])).

fof(f66,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_42344,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_304,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3088,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_306,c_304])).

cnf(c_7426,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | r1_tarski(k9_relat_1(X0,X1),X2)
    | ~ r1_tarski(k1_xboole_0,X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_3088])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1118,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1417,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1418,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1108,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X3),k1_xboole_0)
    | k9_relat_1(X2,X3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1464,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)
    | k9_relat_1(X1,X2) != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_2365,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_305,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3059,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_305,c_304])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4374,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k2_relat_1(k7_relat_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_3059,c_11])).

cnf(c_4872,plain,
    ( r1_tarski(k9_relat_1(X0,X1),X2)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4374,c_3088])).

cnf(c_3357,plain,
    ( ~ r1_tarski(k9_relat_1(X0,X1),X2)
    | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3088,c_11])).

cnf(c_3355,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_3088,c_0])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3730,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_3355,c_3])).

cnf(c_3800,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3730,c_3])).

cnf(c_4154,plain,
    ( ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
    | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3357,c_3800])).

cnf(c_6249,plain,
    ( r1_tarski(k9_relat_1(X0,X1),X2)
    | ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4872,c_4154])).

cnf(c_24773,plain,
    ( r1_tarski(k9_relat_1(X0,X1),X2)
    | ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7426,c_12,c_1417,c_1418,c_2365,c_6249])).

cnf(c_24774,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | r1_tarski(k9_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_24773])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4150,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_3357,c_19])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_681,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_691,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1039,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_681,c_691])).

cnf(c_683,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1051,plain,
    ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1039,c_683])).

cnf(c_1052,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1051])).

cnf(c_4643,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4150,c_1052])).

cnf(c_25148,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_24774,c_4643])).

cnf(c_981,plain,
    ( k7_relat_1(X0,X1) != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_5639,plain,
    ( k7_relat_1(X0,X1) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)),k1_relat_1(sK1))
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_24323,plain,
    ( k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_5639])).

cnf(c_1218,plain,
    ( X0 != X1
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X1
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_1772,plain,
    ( X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_7954,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1147,plain,
    ( v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6158,plain,
    ( v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | ~ v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1124,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_1930,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_4227,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_4228,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4227])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1580,plain,
    ( ~ v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3214,plain,
    ( ~ v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_17,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_988,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
    | ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2387,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_3213,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_859,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2697,plain,
    ( v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1499,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(k7_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2223,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_2225,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_1714,plain,
    ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1212,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1713,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1224,plain,
    ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_940,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1090,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_1223,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1098,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1100,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_894,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1091,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1025,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_874,plain,
    ( v4_relat_1(sK1,X0)
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1024,plain,
    ( v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_945,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k3_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_947,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42344,c_25148,c_24323,c_7954,c_6158,c_4228,c_3214,c_3213,c_2697,c_2225,c_1714,c_1713,c_1418,c_1417,c_1224,c_1223,c_1100,c_1091,c_1025,c_1024,c_947,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.08/1.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/1.94  
% 11.08/1.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.08/1.94  
% 11.08/1.94  ------  iProver source info
% 11.08/1.94  
% 11.08/1.94  git: date: 2020-06-30 10:37:57 +0100
% 11.08/1.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.08/1.94  git: non_committed_changes: false
% 11.08/1.94  git: last_make_outside_of_git: false
% 11.08/1.94  
% 11.08/1.94  ------ 
% 11.08/1.94  ------ Parsing...
% 11.08/1.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.08/1.94  
% 11.08/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.08/1.94  
% 11.08/1.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.08/1.94  
% 11.08/1.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.08/1.94  ------ Proving...
% 11.08/1.94  ------ Problem Properties 
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  clauses                                 21
% 11.08/1.94  conjectures                             3
% 11.08/1.94  EPR                                     5
% 11.08/1.94  Horn                                    20
% 11.08/1.94  unary                                   5
% 11.08/1.94  binary                                  3
% 11.08/1.94  lits                                    52
% 11.08/1.94  lits eq                                 9
% 11.08/1.94  fd_pure                                 0
% 11.08/1.94  fd_pseudo                               0
% 11.08/1.94  fd_cond                                 0
% 11.08/1.94  fd_pseudo_cond                          1
% 11.08/1.94  AC symbols                              0
% 11.08/1.94  
% 11.08/1.94  ------ Input Options Time Limit: Unbounded
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  ------ 
% 11.08/1.94  Current options:
% 11.08/1.94  ------ 
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  ------ Proving...
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  % SZS status Theorem for theBenchmark.p
% 11.08/1.94  
% 11.08/1.94  % SZS output start CNFRefutation for theBenchmark.p
% 11.08/1.94  
% 11.08/1.94  fof(f14,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f28,plain,(
% 11.08/1.94    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f14])).
% 11.08/1.94  
% 11.08/1.94  fof(f39,plain,(
% 11.08/1.94    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(nnf_transformation,[],[f28])).
% 11.08/1.94  
% 11.08/1.94  fof(f61,plain,(
% 11.08/1.94    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f39])).
% 11.08/1.94  
% 11.08/1.94  fof(f12,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f25,plain,(
% 11.08/1.94    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f12])).
% 11.08/1.94  
% 11.08/1.94  fof(f38,plain,(
% 11.08/1.94    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(nnf_transformation,[],[f25])).
% 11.08/1.94  
% 11.08/1.94  fof(f59,plain,(
% 11.08/1.94    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f38])).
% 11.08/1.94  
% 11.08/1.94  fof(f1,axiom,(
% 11.08/1.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f35,plain,(
% 11.08/1.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.08/1.94    inference(nnf_transformation,[],[f1])).
% 11.08/1.94  
% 11.08/1.94  fof(f36,plain,(
% 11.08/1.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.08/1.94    inference(flattening,[],[f35])).
% 11.08/1.94  
% 11.08/1.94  fof(f44,plain,(
% 11.08/1.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f36])).
% 11.08/1.94  
% 11.08/1.94  fof(f43,plain,(
% 11.08/1.94    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.08/1.94    inference(cnf_transformation,[],[f36])).
% 11.08/1.94  
% 11.08/1.94  fof(f74,plain,(
% 11.08/1.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.08/1.94    inference(equality_resolution,[],[f43])).
% 11.08/1.94  
% 11.08/1.94  fof(f11,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f24,plain,(
% 11.08/1.94    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f11])).
% 11.08/1.94  
% 11.08/1.94  fof(f57,plain,(
% 11.08/1.94    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f24])).
% 11.08/1.94  
% 11.08/1.94  fof(f2,axiom,(
% 11.08/1.94    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f45,plain,(
% 11.08/1.94    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f2])).
% 11.08/1.94  
% 11.08/1.94  fof(f17,conjecture,(
% 11.08/1.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f18,negated_conjecture,(
% 11.08/1.94    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 11.08/1.94    inference(negated_conjecture,[],[f17])).
% 11.08/1.94  
% 11.08/1.94  fof(f33,plain,(
% 11.08/1.94    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.08/1.94    inference(ennf_transformation,[],[f18])).
% 11.08/1.94  
% 11.08/1.94  fof(f34,plain,(
% 11.08/1.94    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.08/1.94    inference(flattening,[],[f33])).
% 11.08/1.94  
% 11.08/1.94  fof(f40,plain,(
% 11.08/1.94    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 11.08/1.94    introduced(choice_axiom,[])).
% 11.08/1.94  
% 11.08/1.94  fof(f41,plain,(
% 11.08/1.94    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 11.08/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f40])).
% 11.08/1.94  
% 11.08/1.94  fof(f67,plain,(
% 11.08/1.94    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 11.08/1.94    inference(cnf_transformation,[],[f41])).
% 11.08/1.94  
% 11.08/1.94  fof(f3,axiom,(
% 11.08/1.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f46,plain,(
% 11.08/1.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f3])).
% 11.08/1.94  
% 11.08/1.94  fof(f4,axiom,(
% 11.08/1.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f47,plain,(
% 11.08/1.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f4])).
% 11.08/1.94  
% 11.08/1.94  fof(f5,axiom,(
% 11.08/1.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f48,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f5])).
% 11.08/1.94  
% 11.08/1.94  fof(f6,axiom,(
% 11.08/1.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f49,plain,(
% 11.08/1.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f6])).
% 11.08/1.94  
% 11.08/1.94  fof(f68,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.08/1.94    inference(definition_unfolding,[],[f48,f49])).
% 11.08/1.94  
% 11.08/1.94  fof(f69,plain,(
% 11.08/1.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.08/1.94    inference(definition_unfolding,[],[f47,f68])).
% 11.08/1.94  
% 11.08/1.94  fof(f70,plain,(
% 11.08/1.94    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.08/1.94    inference(definition_unfolding,[],[f46,f69])).
% 11.08/1.94  
% 11.08/1.94  fof(f73,plain,(
% 11.08/1.94    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 11.08/1.94    inference(definition_unfolding,[],[f67,f70,f70])).
% 11.08/1.94  
% 11.08/1.94  fof(f65,plain,(
% 11.08/1.94    v1_relat_1(sK1)),
% 11.08/1.94    inference(cnf_transformation,[],[f41])).
% 11.08/1.94  
% 11.08/1.94  fof(f10,axiom,(
% 11.08/1.94    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f22,plain,(
% 11.08/1.94    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 11.08/1.94    inference(ennf_transformation,[],[f10])).
% 11.08/1.94  
% 11.08/1.94  fof(f23,plain,(
% 11.08/1.94    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 11.08/1.94    inference(flattening,[],[f22])).
% 11.08/1.94  
% 11.08/1.94  fof(f56,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X1) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f23])).
% 11.08/1.94  
% 11.08/1.94  fof(f8,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f20,plain,(
% 11.08/1.94    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f8])).
% 11.08/1.94  
% 11.08/1.94  fof(f37,plain,(
% 11.08/1.94    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(nnf_transformation,[],[f20])).
% 11.08/1.94  
% 11.08/1.94  fof(f51,plain,(
% 11.08/1.94    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f37])).
% 11.08/1.94  
% 11.08/1.94  fof(f15,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f29,plain,(
% 11.08/1.94    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f15])).
% 11.08/1.94  
% 11.08/1.94  fof(f30,plain,(
% 11.08/1.94    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.08/1.94    inference(flattening,[],[f29])).
% 11.08/1.94  
% 11.08/1.94  fof(f63,plain,(
% 11.08/1.94    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f30])).
% 11.08/1.94  
% 11.08/1.94  fof(f9,axiom,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f21,plain,(
% 11.08/1.94    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.08/1.94    inference(ennf_transformation,[],[f9])).
% 11.08/1.94  
% 11.08/1.94  fof(f53,plain,(
% 11.08/1.94    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f21])).
% 11.08/1.94  
% 11.08/1.94  fof(f13,axiom,(
% 11.08/1.94    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f26,plain,(
% 11.08/1.94    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.08/1.94    inference(ennf_transformation,[],[f13])).
% 11.08/1.94  
% 11.08/1.94  fof(f27,plain,(
% 11.08/1.94    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 11.08/1.94    inference(flattening,[],[f26])).
% 11.08/1.94  
% 11.08/1.94  fof(f60,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f27])).
% 11.08/1.94  
% 11.08/1.94  fof(f7,axiom,(
% 11.08/1.94    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f19,plain,(
% 11.08/1.94    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 11.08/1.94    inference(ennf_transformation,[],[f7])).
% 11.08/1.94  
% 11.08/1.94  fof(f50,plain,(
% 11.08/1.94    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f19])).
% 11.08/1.94  
% 11.08/1.94  fof(f71,plain,(
% 11.08/1.94    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 11.08/1.94    inference(definition_unfolding,[],[f50,f70])).
% 11.08/1.94  
% 11.08/1.94  fof(f52,plain,(
% 11.08/1.94    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f37])).
% 11.08/1.94  
% 11.08/1.94  fof(f16,axiom,(
% 11.08/1.94    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 11.08/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.08/1.94  
% 11.08/1.94  fof(f31,plain,(
% 11.08/1.94    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.08/1.94    inference(ennf_transformation,[],[f16])).
% 11.08/1.94  
% 11.08/1.94  fof(f32,plain,(
% 11.08/1.94    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.08/1.94    inference(flattening,[],[f31])).
% 11.08/1.94  
% 11.08/1.94  fof(f64,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.08/1.94    inference(cnf_transformation,[],[f32])).
% 11.08/1.94  
% 11.08/1.94  fof(f72,plain,(
% 11.08/1.94    ( ! [X2,X0,X1] : (k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.08/1.94    inference(definition_unfolding,[],[f64,f69,f69])).
% 11.08/1.94  
% 11.08/1.94  fof(f66,plain,(
% 11.08/1.94    v1_funct_1(sK1)),
% 11.08/1.94    inference(cnf_transformation,[],[f41])).
% 11.08/1.94  
% 11.08/1.94  cnf(c_16,plain,
% 11.08/1.94      ( r1_xboole_0(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0)
% 11.08/1.94      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 11.08/1.94      inference(cnf_transformation,[],[f61]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_42344,plain,
% 11.08/1.94      ( r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.08/1.94      | ~ v1_relat_1(sK1)
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_16]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_12,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0)
% 11.08/1.94      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 11.08/1.94      inference(cnf_transformation,[],[f59]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_306,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.08/1.94      theory(equality) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_304,plain,( X0 = X0 ),theory(equality) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3088,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_306,c_304]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_7426,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.08/1.94      | r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | ~ r1_tarski(k1_xboole_0,X2)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_12,c_3088]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_0,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.08/1.94      inference(cnf_transformation,[],[f44]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1118,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.08/1.94      | ~ r1_tarski(k1_xboole_0,X0)
% 11.08/1.94      | k1_xboole_0 = X0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_0]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1417,plain,
% 11.08/1.94      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.08/1.94      | k1_xboole_0 = k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1118]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1,plain,
% 11.08/1.94      ( r1_tarski(X0,X0) ),
% 11.08/1.94      inference(cnf_transformation,[],[f74]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1418,plain,
% 11.08/1.94      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1108,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1)
% 11.08/1.94      | r1_tarski(k9_relat_1(X2,X3),k1_xboole_0)
% 11.08/1.94      | k9_relat_1(X2,X3) != X0
% 11.08/1.94      | k1_xboole_0 != X1 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_306]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1464,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.08/1.94      | r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)
% 11.08/1.94      | k9_relat_1(X1,X2) != X0
% 11.08/1.94      | k1_xboole_0 != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1108]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_2365,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
% 11.08/1.94      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.08/1.94      | k9_relat_1(X0,X1) != k1_xboole_0
% 11.08/1.94      | k1_xboole_0 != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1464]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_305,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3059,plain,
% 11.08/1.94      ( X0 != X1 | X1 = X0 ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_305,c_304]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_11,plain,
% 11.08/1.94      ( ~ v1_relat_1(X0)
% 11.08/1.94      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.08/1.94      inference(cnf_transformation,[],[f57]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4374,plain,
% 11.08/1.94      ( ~ v1_relat_1(X0)
% 11.08/1.94      | k9_relat_1(X0,X1) = k2_relat_1(k7_relat_1(X0,X1)) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3059,c_11]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4872,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_4374,c_3088]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3357,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3088,c_11]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3355,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1)
% 11.08/1.94      | ~ r1_tarski(X2,X0)
% 11.08/1.94      | ~ r1_tarski(X0,X2)
% 11.08/1.94      | r1_tarski(X2,X1) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3088,c_0]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3,plain,
% 11.08/1.94      ( r1_tarski(k1_xboole_0,X0) ),
% 11.08/1.94      inference(cnf_transformation,[],[f45]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3730,plain,
% 11.08/1.94      ( r1_tarski(X0,X1)
% 11.08/1.94      | ~ r1_tarski(X0,k1_xboole_0)
% 11.08/1.94      | ~ r1_tarski(k1_xboole_0,X1) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3355,c_3]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3800,plain,
% 11.08/1.94      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_xboole_0) ),
% 11.08/1.94      inference(forward_subsumption_resolution,
% 11.08/1.94                [status(thm)],
% 11.08/1.94                [c_3730,c_3]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4154,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
% 11.08/1.94      | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3357,c_3800]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_6249,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_4872,c_4154]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_24773,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(global_propositional_subsumption,
% 11.08/1.94                [status(thm)],
% 11.08/1.94                [c_7426,c_12,c_1417,c_1418,c_2365,c_6249]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_24774,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.08/1.94      | r1_tarski(k9_relat_1(X0,X1),X2)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(renaming,[status(thm)],[c_24773]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_19,negated_conjecture,
% 11.08/1.94      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 11.08/1.94      inference(cnf_transformation,[],[f73]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4150,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_3357,c_19]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_21,negated_conjecture,
% 11.08/1.94      ( v1_relat_1(sK1) ),
% 11.08/1.94      inference(cnf_transformation,[],[f65]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_681,plain,
% 11.08/1.94      ( v1_relat_1(sK1) = iProver_top ),
% 11.08/1.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_691,plain,
% 11.08/1.94      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.08/1.94      | v1_relat_1(X0) != iProver_top ),
% 11.08/1.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1039,plain,
% 11.08/1.94      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 11.08/1.94      inference(superposition,[status(thm)],[c_681,c_691]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_683,plain,
% 11.08/1.94      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 11.08/1.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1051,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 11.08/1.94      inference(demodulation,[status(thm)],[c_1039,c_683]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1052,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 11.08/1.94      inference(predicate_to_equality_rev,[status(thm)],[c_1051]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4643,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 11.08/1.94      inference(global_propositional_subsumption,
% 11.08/1.94                [status(thm)],
% 11.08/1.94                [c_4150,c_1052]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_25148,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k1_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(resolution,[status(thm)],[c_24774,c_4643]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_981,plain,
% 11.08/1.94      ( k7_relat_1(X0,X1) != X2
% 11.08/1.94      | k7_relat_1(X0,X1) = k1_xboole_0
% 11.08/1.94      | k1_xboole_0 != X2 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_305]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_5639,plain,
% 11.08/1.94      ( k7_relat_1(X0,X1) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)),k1_relat_1(sK1))
% 11.08/1.94      | k7_relat_1(X0,X1) = k1_xboole_0
% 11.08/1.94      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)),k1_relat_1(sK1)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_981]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_24323,plain,
% 11.08/1.94      ( k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 11.08/1.94      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_5639]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1218,plain,
% 11.08/1.94      ( X0 != X1
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X1
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_305]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1772,plain,
% 11.08/1.94      ( X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1218]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_7954,plain,
% 11.08/1.94      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1772]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_8,plain,
% 11.08/1.94      ( ~ v4_relat_1(X0,X1)
% 11.08/1.94      | v4_relat_1(k7_relat_1(X0,X2),X1)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(cnf_transformation,[],[f56]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1147,plain,
% 11.08/1.94      ( v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
% 11.08/1.94      | ~ v4_relat_1(sK1,k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_8]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_6158,plain,
% 11.08/1.94      ( v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.08/1.94      | ~ v4_relat_1(sK1,k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1147]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1124,plain,
% 11.08/1.94      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_305]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1930,plain,
% 11.08/1.94      ( X0 != k1_xboole_0
% 11.08/1.94      | k1_xboole_0 = X0
% 11.08/1.94      | k1_xboole_0 != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1124]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4227,plain,
% 11.08/1.94      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
% 11.08/1.94      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1))
% 11.08/1.94      | k1_xboole_0 != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1930]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4228,plain,
% 11.08/1.94      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
% 11.08/1.94      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.08/1.94      | k1_xboole_0 != k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_4227]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_6,plain,
% 11.08/1.94      ( ~ v4_relat_1(X0,X1)
% 11.08/1.94      | r1_tarski(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(cnf_transformation,[],[f51]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1580,plain,
% 11.08/1.94      ( ~ v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
% 11.08/1.94      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_6]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3214,plain,
% 11.08/1.94      ( ~ v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.08/1.94      | r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1580]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_17,plain,
% 11.08/1.94      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0)
% 11.08/1.94      | k7_relat_1(X0,X1) = X0 ),
% 11.08/1.94      inference(cnf_transformation,[],[f63]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_988,plain,
% 11.08/1.94      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
% 11.08/1.94      | ~ v1_relat_1(k7_relat_1(sK1,X0))
% 11.08/1.94      | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_17]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_2387,plain,
% 11.08/1.94      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)
% 11.08/1.94      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_988]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_3213,plain,
% 11.08/1.94      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_2387]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_7,plain,
% 11.08/1.94      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.08/1.94      inference(cnf_transformation,[],[f53]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_859,plain,
% 11.08/1.94      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_7]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_2697,plain,
% 11.08/1.94      ( v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_859]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_14,plain,
% 11.08/1.94      ( ~ r1_xboole_0(X0,X1)
% 11.08/1.94      | ~ v1_relat_1(X2)
% 11.08/1.94      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 11.08/1.94      inference(cnf_transformation,[],[f60]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1499,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(X1)
% 11.08/1.94      | k7_relat_1(k7_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_14]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_2223,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(sK1)
% 11.08/1.94      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1499]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_2225,plain,
% 11.08/1.94      ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(sK1)
% 11.08/1.94      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_2223]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1714,plain,
% 11.08/1.94      ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1212,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_0]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1713,plain,
% 11.08/1.94      ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1212]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1224,plain,
% 11.08/1.94      ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_940,plain,
% 11.08/1.94      ( ~ r1_tarski(X0,X1)
% 11.08/1.94      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.08/1.94      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 11.08/1.94      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != X0 ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_306]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1090,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.08/1.94      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.08/1.94      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 11.08/1.94      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_940]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1223,plain,
% 11.08/1.94      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.08/1.94      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.08/1.94      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.08/1.94      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1090]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_4,plain,
% 11.08/1.94      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 11.08/1.94      inference(cnf_transformation,[],[f71]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1098,plain,
% 11.08/1.94      ( r2_hidden(X0,k1_relat_1(sK1))
% 11.08/1.94      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_relat_1(sK1)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_4]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1100,plain,
% 11.08/1.94      ( r2_hidden(sK0,k1_relat_1(sK1))
% 11.08/1.94      | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1098]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_894,plain,
% 11.08/1.94      ( ~ v1_relat_1(sK1)
% 11.08/1.94      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_11]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1091,plain,
% 11.08/1.94      ( ~ v1_relat_1(sK1)
% 11.08/1.94      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_894]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1025,plain,
% 11.08/1.94      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_1]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_5,plain,
% 11.08/1.94      ( v4_relat_1(X0,X1)
% 11.08/1.94      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.08/1.94      | ~ v1_relat_1(X0) ),
% 11.08/1.94      inference(cnf_transformation,[],[f52]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_874,plain,
% 11.08/1.94      ( v4_relat_1(sK1,X0)
% 11.08/1.94      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_5]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_1024,plain,
% 11.08/1.94      ( v4_relat_1(sK1,k1_relat_1(sK1))
% 11.08/1.94      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_relat_1(sK1) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_874]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_18,plain,
% 11.08/1.94      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.08/1.94      | ~ r2_hidden(X2,k1_relat_1(X1))
% 11.08/1.94      | ~ v1_funct_1(X1)
% 11.08/1.94      | ~ v1_relat_1(X1)
% 11.08/1.94      | k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X0)) ),
% 11.08/1.94      inference(cnf_transformation,[],[f72]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_945,plain,
% 11.08/1.94      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 11.08/1.94      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_funct_1(sK1)
% 11.08/1.94      | ~ v1_relat_1(sK1)
% 11.08/1.94      | k3_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_18]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_947,plain,
% 11.08/1.94      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 11.08/1.94      | ~ v1_funct_1(sK1)
% 11.08/1.94      | ~ v1_relat_1(sK1)
% 11.08/1.94      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.08/1.94      inference(instantiation,[status(thm)],[c_945]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(c_20,negated_conjecture,
% 11.08/1.94      ( v1_funct_1(sK1) ),
% 11.08/1.94      inference(cnf_transformation,[],[f66]) ).
% 11.08/1.94  
% 11.08/1.94  cnf(contradiction,plain,
% 11.08/1.94      ( $false ),
% 11.08/1.94      inference(minisat,
% 11.08/1.94                [status(thm)],
% 11.08/1.94                [c_42344,c_25148,c_24323,c_7954,c_6158,c_4228,c_3214,
% 11.08/1.94                 c_3213,c_2697,c_2225,c_1714,c_1713,c_1418,c_1417,c_1224,
% 11.08/1.94                 c_1223,c_1100,c_1091,c_1025,c_1024,c_947,c_19,c_20,c_21]) ).
% 11.08/1.94  
% 11.08/1.94  
% 11.08/1.94  % SZS output end CNFRefutation for theBenchmark.p
% 11.08/1.94  
% 11.08/1.94  ------                               Statistics
% 11.08/1.94  
% 11.08/1.94  ------ Selected
% 11.08/1.94  
% 11.08/1.94  total_time:                             1.213
% 11.08/1.94  
%------------------------------------------------------------------------------
