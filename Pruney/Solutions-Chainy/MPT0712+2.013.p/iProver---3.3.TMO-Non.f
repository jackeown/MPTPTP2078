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
% DateTime   : Thu Dec  3 11:52:46 EST 2020

% Result     : Timeout 59.75s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  151 ( 304 expanded)
%              Number of clauses        :   95 ( 130 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  409 ( 782 expanded)
%              Number of equality atoms :  148 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32])).

fof(f54,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f59,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f54,f56,f56])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f51,f55,f55])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_351,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_129748,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_137017,plain,
    ( ~ r1_tarski(X0,k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)))
    | r1_tarski(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_129748])).

cnf(c_149188,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)))
    | X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1))
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_137017])).

cnf(c_206527,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X2,X2,X3)),k1_relat_1(sK1)))
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_xboole_0)
    | k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1))
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X2,X2,X3)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_149188])).

cnf(c_206533,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)))
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_206527])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1234,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
    | r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_120891,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1694,plain,
    ( X0 != X1
    | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
    | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_23716,plain,
    ( X0 != X1
    | X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X3,X4,X5)),k1_relat_1(sK1))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X3,X4,X5)),k1_relat_1(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_38860,plain,
    ( X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3)))
    | X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3))) ),
    inference(instantiation,[status(thm)],[c_23716])).

cnf(c_106203,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_38860])).

cnf(c_106204,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_106203])).

cnf(c_3694,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(k7_relat_1(sK1,X2),X3),X4)
    | X4 != X1
    | k7_relat_1(k7_relat_1(sK1,X2),X3) != X0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_10217,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),X4)
    | ~ r1_tarski(k1_xboole_0,X5)
    | X4 != X5
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_41123,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)))
    | ~ r1_tarski(k1_xboole_0,X8)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)) != X8
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10217])).

cnf(c_105185,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_relat_1(sK1)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_relat_1(sK1)) != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_41123])).

cnf(c_105187,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_105185])).

cnf(c_4402,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3)))
    | X0 != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_5599,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2))) != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2)))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4402])).

cnf(c_46967,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5599])).

cnf(c_46969,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_46967])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_741,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X2,k1_relat_1(X1))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_867,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X3),k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_1229,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
    | r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X1)))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_32591,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1122,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
    | ~ v1_relat_1(X3)
    | k7_relat_1(k7_relat_1(X3,k2_enumset1(X0,X0,X0,X1)),X2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1420,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),X2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_2546,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(k7_relat_1(sK1,X2)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_21308,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_349,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1948,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_351,c_349])).

cnf(c_357,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2232,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1948,c_357])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9076,plain,
    ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_2232,c_8])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2217,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_1948,c_8])).

cnf(c_9148,plain,
    ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9076,c_3,c_2217])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1786,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_350,c_0])).

cnf(c_4157,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1786,c_8])).

cnf(c_5938,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4157,c_3])).

cnf(c_9136,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X1) ),
    inference(resolution,[status(thm)],[c_2232,c_5938])).

cnf(c_9162,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k2_relat_1(X0),X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9148,c_9136])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9427,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9162,c_15])).

cnf(c_4391,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1))
    | X0 != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_5435,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4391])).

cnf(c_5437,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5435])).

cnf(c_3501,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1)))
    | X0 != k7_relat_1(sK1,X1)
    | k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1))) != k7_relat_1(sK1,X1) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_5053,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3501])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1132,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4673,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_4065,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_705,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2755,plain,
    ( v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_2541,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_2543,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_777,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
    | ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1131,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_2451,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_655,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_654,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_656,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1063,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_656])).

cnf(c_1559,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_655,c_1063])).

cnf(c_1515,plain,
    ( r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_979,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1514,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_991,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_736,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_859,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_990,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_873,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r2_hidden(X1,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_875,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_715,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_860,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_209,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ r2_hidden(X0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_205,c_17])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_212,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_206533,c_120891,c_106204,c_105187,c_46969,c_32591,c_21308,c_9427,c_5437,c_5053,c_4673,c_4065,c_2755,c_2543,c_2451,c_1559,c_1515,c_1514,c_991,c_990,c_875,c_860,c_212,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  % Running in FOF mode
% 59.75/8.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.75/8.00  
% 59.75/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.75/8.00  
% 59.75/8.00  ------  iProver source info
% 59.75/8.00  
% 59.75/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.75/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.75/8.00  git: non_committed_changes: false
% 59.75/8.00  git: last_make_outside_of_git: false
% 59.75/8.00  
% 59.75/8.00  ------ 
% 59.75/8.00  ------ Parsing...
% 59.75/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.75/8.00  
% 59.75/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.75/8.00  
% 59.75/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.75/8.00  
% 59.75/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.75/8.00  ------ Proving...
% 59.75/8.00  ------ Problem Properties 
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  clauses                                 16
% 59.75/8.00  conjectures                             2
% 59.75/8.00  EPR                                     4
% 59.75/8.00  Horn                                    15
% 59.75/8.00  unary                                   6
% 59.75/8.00  binary                                  2
% 59.75/8.00  lits                                    35
% 59.75/8.00  lits eq                                 7
% 59.75/8.00  fd_pure                                 0
% 59.75/8.00  fd_pseudo                               0
% 59.75/8.00  fd_cond                                 0
% 59.75/8.00  fd_pseudo_cond                          1
% 59.75/8.00  AC symbols                              0
% 59.75/8.00  
% 59.75/8.00  ------ Input Options Time Limit: Unbounded
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  ------ 
% 59.75/8.00  Current options:
% 59.75/8.00  ------ 
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  ------ Proving...
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  % SZS status Theorem for theBenchmark.p
% 59.75/8.00  
% 59.75/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 59.75/8.00  
% 59.75/8.00  fof(f11,axiom,(
% 59.75/8.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f21,plain,(
% 59.75/8.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(ennf_transformation,[],[f11])).
% 59.75/8.00  
% 59.75/8.00  fof(f30,plain,(
% 59.75/8.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(nnf_transformation,[],[f21])).
% 59.75/8.00  
% 59.75/8.00  fof(f31,plain,(
% 59.75/8.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(flattening,[],[f30])).
% 59.75/8.00  
% 59.75/8.00  fof(f48,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f31])).
% 59.75/8.00  
% 59.75/8.00  fof(f6,axiom,(
% 59.75/8.00    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f16,plain,(
% 59.75/8.00    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 59.75/8.00    inference(ennf_transformation,[],[f6])).
% 59.75/8.00  
% 59.75/8.00  fof(f41,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f16])).
% 59.75/8.00  
% 59.75/8.00  fof(f4,axiom,(
% 59.75/8.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f39,plain,(
% 59.75/8.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f4])).
% 59.75/8.00  
% 59.75/8.00  fof(f5,axiom,(
% 59.75/8.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f40,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f5])).
% 59.75/8.00  
% 59.75/8.00  fof(f55,plain,(
% 59.75/8.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 59.75/8.00    inference(definition_unfolding,[],[f39,f40])).
% 59.75/8.00  
% 59.75/8.00  fof(f57,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 59.75/8.00    inference(definition_unfolding,[],[f41,f55])).
% 59.75/8.00  
% 59.75/8.00  fof(f9,axiom,(
% 59.75/8.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f19,plain,(
% 59.75/8.00    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(ennf_transformation,[],[f9])).
% 59.75/8.00  
% 59.75/8.00  fof(f20,plain,(
% 59.75/8.00    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(flattening,[],[f19])).
% 59.75/8.00  
% 59.75/8.00  fof(f44,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f20])).
% 59.75/8.00  
% 59.75/8.00  fof(f10,axiom,(
% 59.75/8.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f46,plain,(
% 59.75/8.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 59.75/8.00    inference(cnf_transformation,[],[f10])).
% 59.75/8.00  
% 59.75/8.00  fof(f2,axiom,(
% 59.75/8.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f37,plain,(
% 59.75/8.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f2])).
% 59.75/8.00  
% 59.75/8.00  fof(f1,axiom,(
% 59.75/8.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f28,plain,(
% 59.75/8.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.75/8.00    inference(nnf_transformation,[],[f1])).
% 59.75/8.00  
% 59.75/8.00  fof(f29,plain,(
% 59.75/8.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.75/8.00    inference(flattening,[],[f28])).
% 59.75/8.00  
% 59.75/8.00  fof(f36,plain,(
% 59.75/8.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f29])).
% 59.75/8.00  
% 59.75/8.00  fof(f14,conjecture,(
% 59.75/8.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f15,negated_conjecture,(
% 59.75/8.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 59.75/8.00    inference(negated_conjecture,[],[f14])).
% 59.75/8.00  
% 59.75/8.00  fof(f26,plain,(
% 59.75/8.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 59.75/8.00    inference(ennf_transformation,[],[f15])).
% 59.75/8.00  
% 59.75/8.00  fof(f27,plain,(
% 59.75/8.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 59.75/8.00    inference(flattening,[],[f26])).
% 59.75/8.00  
% 59.75/8.00  fof(f32,plain,(
% 59.75/8.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 59.75/8.00    introduced(choice_axiom,[])).
% 59.75/8.00  
% 59.75/8.00  fof(f33,plain,(
% 59.75/8.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 59.75/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32])).
% 59.75/8.00  
% 59.75/8.00  fof(f54,plain,(
% 59.75/8.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 59.75/8.00    inference(cnf_transformation,[],[f33])).
% 59.75/8.00  
% 59.75/8.00  fof(f3,axiom,(
% 59.75/8.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f38,plain,(
% 59.75/8.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f3])).
% 59.75/8.00  
% 59.75/8.00  fof(f56,plain,(
% 59.75/8.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 59.75/8.00    inference(definition_unfolding,[],[f38,f55])).
% 59.75/8.00  
% 59.75/8.00  fof(f59,plain,(
% 59.75/8.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 59.75/8.00    inference(definition_unfolding,[],[f54,f56,f56])).
% 59.75/8.00  
% 59.75/8.00  fof(f35,plain,(
% 59.75/8.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 59.75/8.00    inference(cnf_transformation,[],[f29])).
% 59.75/8.00  
% 59.75/8.00  fof(f60,plain,(
% 59.75/8.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 59.75/8.00    inference(equality_resolution,[],[f35])).
% 59.75/8.00  
% 59.75/8.00  fof(f7,axiom,(
% 59.75/8.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f17,plain,(
% 59.75/8.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 59.75/8.00    inference(ennf_transformation,[],[f7])).
% 59.75/8.00  
% 59.75/8.00  fof(f42,plain,(
% 59.75/8.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f17])).
% 59.75/8.00  
% 59.75/8.00  fof(f12,axiom,(
% 59.75/8.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f22,plain,(
% 59.75/8.00    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.75/8.00    inference(ennf_transformation,[],[f12])).
% 59.75/8.00  
% 59.75/8.00  fof(f23,plain,(
% 59.75/8.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 59.75/8.00    inference(flattening,[],[f22])).
% 59.75/8.00  
% 59.75/8.00  fof(f50,plain,(
% 59.75/8.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f23])).
% 59.75/8.00  
% 59.75/8.00  fof(f8,axiom,(
% 59.75/8.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f18,plain,(
% 59.75/8.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.75/8.00    inference(ennf_transformation,[],[f8])).
% 59.75/8.00  
% 59.75/8.00  fof(f43,plain,(
% 59.75/8.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f18])).
% 59.75/8.00  
% 59.75/8.00  fof(f13,axiom,(
% 59.75/8.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 59.75/8.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.75/8.00  
% 59.75/8.00  fof(f24,plain,(
% 59.75/8.00    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 59.75/8.00    inference(ennf_transformation,[],[f13])).
% 59.75/8.00  
% 59.75/8.00  fof(f25,plain,(
% 59.75/8.00    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 59.75/8.00    inference(flattening,[],[f24])).
% 59.75/8.00  
% 59.75/8.00  fof(f51,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 59.75/8.00    inference(cnf_transformation,[],[f25])).
% 59.75/8.00  
% 59.75/8.00  fof(f58,plain,(
% 59.75/8.00    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 59.75/8.00    inference(definition_unfolding,[],[f51,f55,f55])).
% 59.75/8.00  
% 59.75/8.00  fof(f53,plain,(
% 59.75/8.00    v1_funct_1(sK1)),
% 59.75/8.00    inference(cnf_transformation,[],[f33])).
% 59.75/8.00  
% 59.75/8.00  fof(f52,plain,(
% 59.75/8.00    v1_relat_1(sK1)),
% 59.75/8.00    inference(cnf_transformation,[],[f33])).
% 59.75/8.00  
% 59.75/8.00  cnf(c_351,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.75/8.00      theory(equality) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_129748,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1)
% 59.75/8.00      | r1_tarski(X2,k1_xboole_0)
% 59.75/8.00      | X2 != X0
% 59.75/8.00      | k1_xboole_0 != X1 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_351]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_137017,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)))
% 59.75/8.00      | r1_tarski(X3,k1_xboole_0)
% 59.75/8.00      | X3 != X0
% 59.75/8.00      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_129748]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_149188,plain,
% 59.75/8.00      ( r1_tarski(X0,k1_xboole_0)
% 59.75/8.00      | ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)))
% 59.75/8.00      | X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1))
% 59.75/8.00      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_137017]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_206527,plain,
% 59.75/8.00      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X2,X2,X3)),k1_relat_1(sK1)))
% 59.75/8.00      | r1_tarski(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_xboole_0)
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1))
% 59.75/8.00      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X2,X2,X3)),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_149188]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_206533,plain,
% 59.75/8.00      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)))
% 59.75/8.00      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 59.75/8.00      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_206527]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_11,plain,
% 59.75/8.00      ( r2_hidden(X0,k1_relat_1(X1))
% 59.75/8.00      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 59.75/8.00      | ~ v1_relat_1(X1) ),
% 59.75/8.00      inference(cnf_transformation,[],[f48]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1234,plain,
% 59.75/8.00      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
% 59.75/8.00      | r2_hidden(X0,k1_relat_1(sK1))
% 59.75/8.00      | ~ v1_relat_1(sK1) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_11]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_120891,plain,
% 59.75/8.00      ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | r2_hidden(sK0,k1_relat_1(sK1))
% 59.75/8.00      | ~ v1_relat_1(sK1) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1234]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1694,plain,
% 59.75/8.00      ( X0 != X1
% 59.75/8.00      | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_350]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_23716,plain,
% 59.75/8.00      ( X0 != X1
% 59.75/8.00      | X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X3,X4,X5)),k1_relat_1(sK1))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X2,X3,X4,X5)),k1_relat_1(sK1)) != X1 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1694]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_38860,plain,
% 59.75/8.00      ( X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3)))
% 59.75/8.00      | X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_23716]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_106203,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_38860]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_106204,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_106203]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_3694,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1)
% 59.75/8.00      | r1_tarski(k7_relat_1(k7_relat_1(sK1,X2),X3),X4)
% 59.75/8.00      | X4 != X1
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,X2),X3) != X0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_351]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_10217,plain,
% 59.75/8.00      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),X4)
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,X5)
% 59.75/8.00      | X4 != X5
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_3694]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_41123,plain,
% 59.75/8.00      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)))
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,X8)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X5,X6,X7)),k1_relat_1(sK1)) != X8
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_10217]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_105185,plain,
% 59.75/8.00      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_relat_1(sK1)))
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X4,X4,X4,X5)),k1_relat_1(sK1)) != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X1,X2,X3)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_41123]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_105187,plain,
% 59.75/8.00      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)))
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_105185]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4402,plain,
% 59.75/8.00      ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3)))
% 59.75/8.00      | X0 != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(k7_relat_1(sK1,X3))) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1694]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5599,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2))) != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2)))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X3,X3,X3,X4)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_4402]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_46967,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_5599]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_46969,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_46967]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4,plain,
% 59.75/8.00      ( r2_hidden(X0,X1)
% 59.75/8.00      | r2_hidden(X2,X1)
% 59.75/8.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
% 59.75/8.00      inference(cnf_transformation,[],[f57]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_741,plain,
% 59.75/8.00      ( r2_hidden(X0,k1_relat_1(X1))
% 59.75/8.00      | r2_hidden(X2,k1_relat_1(X1))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),k1_relat_1(X1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_867,plain,
% 59.75/8.00      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 59.75/8.00      | r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X3),k1_relat_1(k7_relat_1(X1,X2))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_741]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1229,plain,
% 59.75/8.00      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
% 59.75/8.00      | r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X1)))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),k1_relat_1(k7_relat_1(sK1,X1))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_867]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_32591,plain,
% 59.75/8.00      ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1229]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_7,plain,
% 59.75/8.00      ( ~ r1_xboole_0(X0,X1)
% 59.75/8.00      | ~ v1_relat_1(X2)
% 59.75/8.00      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 59.75/8.00      inference(cnf_transformation,[],[f44]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1122,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
% 59.75/8.00      | ~ v1_relat_1(X3)
% 59.75/8.00      | k7_relat_1(k7_relat_1(X3,k2_enumset1(X0,X0,X0,X1)),X2) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_7]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1420,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),X2) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1122]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2546,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(k7_relat_1(sK1,X2)))
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k7_relat_1(sK1,X2))) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1420]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_21308,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_2546]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_349,plain,( X0 = X0 ),theory(equality) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1948,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_351,c_349]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_357,plain,
% 59.75/8.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 59.75/8.00      theory(equality) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2232,plain,
% 59.75/8.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 59.75/8.00      | r1_tarski(k2_relat_1(X2),X1)
% 59.75/8.00      | X2 != X0 ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_1948,c_357]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_8,plain,
% 59.75/8.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 59.75/8.00      inference(cnf_transformation,[],[f46]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_9076,plain,
% 59.75/8.00      ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0)
% 59.75/8.00      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_2232,c_8]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_3,plain,
% 59.75/8.00      ( r1_tarski(k1_xboole_0,X0) ),
% 59.75/8.00      inference(cnf_transformation,[],[f37]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2217,plain,
% 59.75/8.00      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,X0) ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_1948,c_8]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_9148,plain,
% 59.75/8.00      ( r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
% 59.75/8.00      inference(global_propositional_subsumption,
% 59.75/8.00                [status(thm)],
% 59.75/8.00                [c_9076,c_3,c_2217]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_0,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 59.75/8.00      inference(cnf_transformation,[],[f36]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1786,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_350,c_0]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4157,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 59.75/8.00      | ~ r1_tarski(k1_xboole_0,X0)
% 59.75/8.00      | X0 = k2_relat_1(k1_xboole_0) ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_1786,c_8]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5938,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k2_relat_1(k1_xboole_0) ),
% 59.75/8.00      inference(global_propositional_subsumption,
% 59.75/8.00                [status(thm)],
% 59.75/8.00                [c_4157,c_3]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_9136,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 59.75/8.00      | r1_tarski(k2_relat_1(X0),X1)
% 59.75/8.00      | ~ r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X1) ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_2232,c_5938]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_9162,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(k2_relat_1(X0),X1) ),
% 59.75/8.00      inference(backward_subsumption_resolution,
% 59.75/8.00                [status(thm)],
% 59.75/8.00                [c_9148,c_9136]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_15,negated_conjecture,
% 59.75/8.00      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 59.75/8.00      inference(cnf_transformation,[],[f59]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_9427,plain,
% 59.75/8.00      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
% 59.75/8.00      inference(resolution,[status(thm)],[c_9162,c_15]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4391,plain,
% 59.75/8.00      ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1))
% 59.75/8.00      | X0 != k1_xboole_0
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X2)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1694]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5435,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
% 59.75/8.00      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1))
% 59.75/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_4391]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5437,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
% 59.75/8.00      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 59.75/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_5435]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_3501,plain,
% 59.75/8.00      ( X0 = k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1)))
% 59.75/8.00      | X0 != k7_relat_1(sK1,X1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1))) != k7_relat_1(sK1,X1) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1694]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5053,plain,
% 59.75/8.00      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_3501]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1,plain,
% 59.75/8.00      ( r1_tarski(X0,X0) ),
% 59.75/8.00      inference(cnf_transformation,[],[f60]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1132,plain,
% 59.75/8.00      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4673,plain,
% 59.75/8.00      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1132]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_4065,plain,
% 59.75/8.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_5,plain,
% 59.75/8.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 59.75/8.00      inference(cnf_transformation,[],[f42]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_705,plain,
% 59.75/8.00      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_5]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2755,plain,
% 59.75/8.00      ( v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 59.75/8.00      | ~ v1_relat_1(sK1) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_705]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2541,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1420]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2543,plain,
% 59.75/8.00      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_2541]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_13,plain,
% 59.75/8.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 59.75/8.00      | ~ v1_relat_1(X0)
% 59.75/8.00      | k7_relat_1(X0,X1) = X0 ),
% 59.75/8.00      inference(cnf_transformation,[],[f50]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_777,plain,
% 59.75/8.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
% 59.75/8.00      | ~ v1_relat_1(k7_relat_1(sK1,X0))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_13]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1131,plain,
% 59.75/8.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)))
% 59.75/8.00      | ~ v1_relat_1(k7_relat_1(sK1,X0))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_777]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_2451,plain,
% 59.75/8.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 59.75/8.00      | ~ v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 59.75/8.00      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1131]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_655,plain,
% 59.75/8.00      ( r1_tarski(X0,X0) = iProver_top ),
% 59.75/8.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_654,plain,
% 59.75/8.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 59.75/8.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_656,plain,
% 59.75/8.00      ( X0 = X1
% 59.75/8.00      | r1_tarski(X0,X1) != iProver_top
% 59.75/8.00      | r1_tarski(X1,X0) != iProver_top ),
% 59.75/8.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1063,plain,
% 59.75/8.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 59.75/8.00      inference(superposition,[status(thm)],[c_654,c_656]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1559,plain,
% 59.75/8.00      ( k1_xboole_0 = k1_xboole_0 ),
% 59.75/8.00      inference(superposition,[status(thm)],[c_655,c_1063]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1515,plain,
% 59.75/8.00      ( r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_979,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 59.75/8.00      | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_0]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_1514,plain,
% 59.75/8.00      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 59.75/8.00      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_979]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_991,plain,
% 59.75/8.00      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_736,plain,
% 59.75/8.00      ( ~ r1_tarski(X0,X1)
% 59.75/8.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 59.75/8.00      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_351]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_859,plain,
% 59.75/8.00      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 59.75/8.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 59.75/8.00      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_736]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_990,plain,
% 59.75/8.00      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 59.75/8.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 59.75/8.00      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_859]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_873,plain,
% 59.75/8.00      ( r2_hidden(X0,k1_relat_1(sK1))
% 59.75/8.00      | r2_hidden(X1,k1_relat_1(sK1))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_741]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_875,plain,
% 59.75/8.00      ( r2_hidden(sK0,k1_relat_1(sK1))
% 59.75/8.00      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_873]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_6,plain,
% 59.75/8.00      ( ~ v1_relat_1(X0)
% 59.75/8.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 59.75/8.00      inference(cnf_transformation,[],[f43]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_715,plain,
% 59.75/8.00      ( ~ v1_relat_1(sK1)
% 59.75/8.00      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_860,plain,
% 59.75/8.00      ( ~ v1_relat_1(sK1)
% 59.75/8.00      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_715]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_14,plain,
% 59.75/8.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 59.75/8.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 59.75/8.00      | ~ v1_funct_1(X1)
% 59.75/8.00      | ~ v1_relat_1(X1)
% 59.75/8.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2)) ),
% 59.75/8.00      inference(cnf_transformation,[],[f58]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_16,negated_conjecture,
% 59.75/8.00      ( v1_funct_1(sK1) ),
% 59.75/8.00      inference(cnf_transformation,[],[f53]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_204,plain,
% 59.75/8.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 59.75/8.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 59.75/8.00      | ~ v1_relat_1(X1)
% 59.75/8.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2))
% 59.75/8.00      | sK1 != X1 ),
% 59.75/8.00      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_205,plain,
% 59.75/8.00      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 59.75/8.00      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 59.75/8.00      | ~ v1_relat_1(sK1)
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 59.75/8.00      inference(unflattening,[status(thm)],[c_204]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_17,negated_conjecture,
% 59.75/8.00      ( v1_relat_1(sK1) ),
% 59.75/8.00      inference(cnf_transformation,[],[f52]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_209,plain,
% 59.75/8.00      ( ~ r2_hidden(X1,k1_relat_1(sK1))
% 59.75/8.00      | ~ r2_hidden(X0,k1_relat_1(sK1))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 59.75/8.00      inference(global_propositional_subsumption,
% 59.75/8.00                [status(thm)],
% 59.75/8.00                [c_205,c_17]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_210,plain,
% 59.75/8.00      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 59.75/8.00      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 59.75/8.00      inference(renaming,[status(thm)],[c_209]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(c_212,plain,
% 59.75/8.00      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 59.75/8.00      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 59.75/8.00      inference(instantiation,[status(thm)],[c_210]) ).
% 59.75/8.00  
% 59.75/8.00  cnf(contradiction,plain,
% 59.75/8.00      ( $false ),
% 59.75/8.00      inference(minisat,
% 59.75/8.00                [status(thm)],
% 59.75/8.00                [c_206533,c_120891,c_106204,c_105187,c_46969,c_32591,
% 59.75/8.00                 c_21308,c_9427,c_5437,c_5053,c_4673,c_4065,c_2755,
% 59.75/8.00                 c_2543,c_2451,c_1559,c_1515,c_1514,c_991,c_990,c_875,
% 59.75/8.00                 c_860,c_212,c_15,c_17]) ).
% 59.75/8.00  
% 59.75/8.00  
% 59.75/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 59.75/8.00  
% 59.75/8.00  ------                               Statistics
% 59.75/8.00  
% 59.75/8.00  ------ Selected
% 59.75/8.00  
% 59.75/8.00  total_time:                             7.282
% 59.75/8.00  
%------------------------------------------------------------------------------
