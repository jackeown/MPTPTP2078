%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:46 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 288 expanded)
%              Number of clauses        :   85 ( 118 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  388 ( 673 expanded)
%              Number of equality atoms :  135 ( 282 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f35])).

fof(f60,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f66,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f60,f63,f63])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f57,f62,f62])).

fof(f59,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_255,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1122,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK1,X2)
    | k7_relat_1(sK1,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1929,plain,
    ( X0 != k7_relat_1(X1,X2)
    | X0 = k7_relat_1(sK1,X3)
    | k7_relat_1(sK1,X3) != k7_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_9677,plain,
    ( X0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | X0 = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_40571,plain,
    ( k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_9677])).

cnf(c_254,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2958,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_255,c_254])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4561,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2958,c_13])).

cnf(c_264,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2961,plain,
    ( X0 != X1
    | X2 != k2_relat_1(X1)
    | k2_relat_1(X0) = X2 ),
    inference(resolution,[status(thm)],[c_255,c_264])).

cnf(c_28418,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4561,c_2961])).

cnf(c_2952,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_255,c_13])).

cnf(c_4574,plain,
    ( X0 = k2_relat_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2958,c_2952])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2997,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_256,c_254])).

cnf(c_4591,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4574,c_2997])).

cnf(c_3645,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2997,c_13])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3762,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_3])).

cnf(c_9609,plain,
    ( r1_tarski(X0,X1)
    | X0 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4591,c_3762])).

cnf(c_33793,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28418,c_9609])).

cnf(c_28376,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_4561,c_255])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2942,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_255,c_0])).

cnf(c_11443,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2942,c_13])).

cnf(c_14712,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11443,c_3])).

cnf(c_32961,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_28376,c_14712])).

cnf(c_33305,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32961,c_2958])).

cnf(c_34274,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k2_relat_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_33793,c_33305])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35350,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34274,c_17])).

cnf(c_1638,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X2)
    | X2 != X1
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_4009,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X1)
    | X1 != X0
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_10497,plain,
    ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4009])).

cnf(c_27120,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_10497])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_954,plain,
    ( v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6990,plain,
    ( v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | ~ v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1007,plain,
    ( X0 != X1
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X1
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1650,plain,
    ( X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_6150,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_5615,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_1865,plain,
    ( X0 != X1
    | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
    | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_4414,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X2)),k1_relat_1(sK1))
    | X0 != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X2)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_5614,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4414])).

cnf(c_5616,plain,
    ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5614])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1268,plain,
    ( ~ v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3419,plain,
    ( ~ v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_833,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
    | ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2189,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_3418,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_727,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2592,plain,
    ( v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1496,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1))
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2078,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2080,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1633,plain,
    ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1001,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1632,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1059,plain,
    ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_770,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_934,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1058,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_942,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r2_hidden(X1,k1_relat_1(sK1))
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_944,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_760,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_935,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_870,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_755,plain,
    ( v4_relat_1(sK1,X0)
    | ~ r1_tarski(k1_relat_1(sK1),X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_869,plain,
    ( v4_relat_1(sK1,k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_797,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k3_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_799,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40571,c_35350,c_27120,c_6990,c_6150,c_5615,c_5616,c_3419,c_3418,c_2592,c_2080,c_1633,c_1632,c_1059,c_1058,c_944,c_935,c_870,c_869,c_799,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.68/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/2.00  
% 11.68/2.00  ------  iProver source info
% 11.68/2.00  
% 11.68/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.68/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/2.00  git: non_committed_changes: false
% 11.68/2.00  git: last_make_outside_of_git: false
% 11.68/2.00  
% 11.68/2.00  ------ 
% 11.68/2.00  
% 11.68/2.00  ------ Input Options
% 11.68/2.00  
% 11.68/2.00  --out_options                           all
% 11.68/2.00  --tptp_safe_out                         true
% 11.68/2.00  --problem_path                          ""
% 11.68/2.00  --include_path                          ""
% 11.68/2.00  --clausifier                            res/vclausify_rel
% 11.68/2.00  --clausifier_options                    --mode clausify
% 11.68/2.00  --stdin                                 false
% 11.68/2.00  --stats_out                             sel
% 11.68/2.00  
% 11.68/2.00  ------ General Options
% 11.68/2.00  
% 11.68/2.00  --fof                                   false
% 11.68/2.00  --time_out_real                         604.99
% 11.68/2.00  --time_out_virtual                      -1.
% 11.68/2.00  --symbol_type_check                     false
% 11.68/2.00  --clausify_out                          false
% 11.68/2.00  --sig_cnt_out                           false
% 11.68/2.00  --trig_cnt_out                          false
% 11.68/2.00  --trig_cnt_out_tolerance                1.
% 11.68/2.00  --trig_cnt_out_sk_spl                   false
% 11.68/2.00  --abstr_cl_out                          false
% 11.68/2.00  
% 11.68/2.00  ------ Global Options
% 11.68/2.00  
% 11.68/2.00  --schedule                              none
% 11.68/2.00  --add_important_lit                     false
% 11.68/2.00  --prop_solver_per_cl                    1000
% 11.68/2.00  --min_unsat_core                        false
% 11.68/2.00  --soft_assumptions                      false
% 11.68/2.00  --soft_lemma_size                       3
% 11.68/2.00  --prop_impl_unit_size                   0
% 11.68/2.00  --prop_impl_unit                        []
% 11.68/2.00  --share_sel_clauses                     true
% 11.68/2.00  --reset_solvers                         false
% 11.68/2.00  --bc_imp_inh                            [conj_cone]
% 11.68/2.00  --conj_cone_tolerance                   3.
% 11.68/2.00  --extra_neg_conj                        none
% 11.68/2.00  --large_theory_mode                     true
% 11.68/2.00  --prolific_symb_bound                   200
% 11.68/2.00  --lt_threshold                          2000
% 11.68/2.00  --clause_weak_htbl                      true
% 11.68/2.00  --gc_record_bc_elim                     false
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing Options
% 11.68/2.00  
% 11.68/2.00  --preprocessing_flag                    true
% 11.68/2.00  --time_out_prep_mult                    0.1
% 11.68/2.00  --splitting_mode                        input
% 11.68/2.00  --splitting_grd                         true
% 11.68/2.00  --splitting_cvd                         false
% 11.68/2.00  --splitting_cvd_svl                     false
% 11.68/2.00  --splitting_nvd                         32
% 11.68/2.00  --sub_typing                            true
% 11.68/2.00  --prep_gs_sim                           false
% 11.68/2.00  --prep_unflatten                        true
% 11.68/2.00  --prep_res_sim                          true
% 11.68/2.00  --prep_upred                            true
% 11.68/2.00  --prep_sem_filter                       exhaustive
% 11.68/2.00  --prep_sem_filter_out                   false
% 11.68/2.00  --pred_elim                             false
% 11.68/2.00  --res_sim_input                         true
% 11.68/2.00  --eq_ax_congr_red                       true
% 11.68/2.00  --pure_diseq_elim                       true
% 11.68/2.00  --brand_transform                       false
% 11.68/2.00  --non_eq_to_eq                          false
% 11.68/2.00  --prep_def_merge                        true
% 11.68/2.00  --prep_def_merge_prop_impl              false
% 11.68/2.00  --prep_def_merge_mbd                    true
% 11.68/2.00  --prep_def_merge_tr_red                 false
% 11.68/2.00  --prep_def_merge_tr_cl                  false
% 11.68/2.00  --smt_preprocessing                     true
% 11.68/2.00  --smt_ac_axioms                         fast
% 11.68/2.00  --preprocessed_out                      false
% 11.68/2.00  --preprocessed_stats                    false
% 11.68/2.00  
% 11.68/2.00  ------ Abstraction refinement Options
% 11.68/2.00  
% 11.68/2.00  --abstr_ref                             []
% 11.68/2.00  --abstr_ref_prep                        false
% 11.68/2.00  --abstr_ref_until_sat                   false
% 11.68/2.00  --abstr_ref_sig_restrict                funpre
% 11.68/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/2.00  --abstr_ref_under                       []
% 11.68/2.00  
% 11.68/2.00  ------ SAT Options
% 11.68/2.00  
% 11.68/2.00  --sat_mode                              false
% 11.68/2.00  --sat_fm_restart_options                ""
% 11.68/2.00  --sat_gr_def                            false
% 11.68/2.00  --sat_epr_types                         true
% 11.68/2.00  --sat_non_cyclic_types                  false
% 11.68/2.00  --sat_finite_models                     false
% 11.68/2.00  --sat_fm_lemmas                         false
% 11.68/2.00  --sat_fm_prep                           false
% 11.68/2.00  --sat_fm_uc_incr                        true
% 11.68/2.00  --sat_out_model                         small
% 11.68/2.00  --sat_out_clauses                       false
% 11.68/2.00  
% 11.68/2.00  ------ QBF Options
% 11.68/2.00  
% 11.68/2.00  --qbf_mode                              false
% 11.68/2.00  --qbf_elim_univ                         false
% 11.68/2.00  --qbf_dom_inst                          none
% 11.68/2.00  --qbf_dom_pre_inst                      false
% 11.68/2.00  --qbf_sk_in                             false
% 11.68/2.00  --qbf_pred_elim                         true
% 11.68/2.00  --qbf_split                             512
% 11.68/2.00  
% 11.68/2.00  ------ BMC1 Options
% 11.68/2.00  
% 11.68/2.00  --bmc1_incremental                      false
% 11.68/2.00  --bmc1_axioms                           reachable_all
% 11.68/2.00  --bmc1_min_bound                        0
% 11.68/2.00  --bmc1_max_bound                        -1
% 11.68/2.00  --bmc1_max_bound_default                -1
% 11.68/2.00  --bmc1_symbol_reachability              true
% 11.68/2.00  --bmc1_property_lemmas                  false
% 11.68/2.00  --bmc1_k_induction                      false
% 11.68/2.00  --bmc1_non_equiv_states                 false
% 11.68/2.00  --bmc1_deadlock                         false
% 11.68/2.00  --bmc1_ucm                              false
% 11.68/2.00  --bmc1_add_unsat_core                   none
% 11.68/2.00  --bmc1_unsat_core_children              false
% 11.68/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/2.00  --bmc1_out_stat                         full
% 11.68/2.00  --bmc1_ground_init                      false
% 11.68/2.00  --bmc1_pre_inst_next_state              false
% 11.68/2.00  --bmc1_pre_inst_state                   false
% 11.68/2.00  --bmc1_pre_inst_reach_state             false
% 11.68/2.00  --bmc1_out_unsat_core                   false
% 11.68/2.00  --bmc1_aig_witness_out                  false
% 11.68/2.00  --bmc1_verbose                          false
% 11.68/2.00  --bmc1_dump_clauses_tptp                false
% 11.68/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.68/2.00  --bmc1_dump_file                        -
% 11.68/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.68/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.68/2.00  --bmc1_ucm_extend_mode                  1
% 11.68/2.00  --bmc1_ucm_init_mode                    2
% 11.68/2.00  --bmc1_ucm_cone_mode                    none
% 11.68/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.68/2.00  --bmc1_ucm_relax_model                  4
% 11.68/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.68/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/2.00  --bmc1_ucm_layered_model                none
% 11.68/2.00  --bmc1_ucm_max_lemma_size               10
% 11.68/2.00  
% 11.68/2.00  ------ AIG Options
% 11.68/2.00  
% 11.68/2.00  --aig_mode                              false
% 11.68/2.00  
% 11.68/2.00  ------ Instantiation Options
% 11.68/2.00  
% 11.68/2.00  --instantiation_flag                    true
% 11.68/2.00  --inst_sos_flag                         false
% 11.68/2.00  --inst_sos_phase                        true
% 11.68/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/2.00  --inst_lit_sel_side                     num_symb
% 11.68/2.00  --inst_solver_per_active                1400
% 11.68/2.00  --inst_solver_calls_frac                1.
% 11.68/2.00  --inst_passive_queue_type               priority_queues
% 11.68/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/2.00  --inst_passive_queues_freq              [25;2]
% 11.68/2.00  --inst_dismatching                      true
% 11.68/2.00  --inst_eager_unprocessed_to_passive     true
% 11.68/2.00  --inst_prop_sim_given                   true
% 11.68/2.00  --inst_prop_sim_new                     false
% 11.68/2.00  --inst_subs_new                         false
% 11.68/2.00  --inst_eq_res_simp                      false
% 11.68/2.00  --inst_subs_given                       false
% 11.68/2.00  --inst_orphan_elimination               true
% 11.68/2.00  --inst_learning_loop_flag               true
% 11.68/2.00  --inst_learning_start                   3000
% 11.68/2.00  --inst_learning_factor                  2
% 11.68/2.00  --inst_start_prop_sim_after_learn       3
% 11.68/2.00  --inst_sel_renew                        solver
% 11.68/2.00  --inst_lit_activity_flag                true
% 11.68/2.00  --inst_restr_to_given                   false
% 11.68/2.00  --inst_activity_threshold               500
% 11.68/2.00  --inst_out_proof                        true
% 11.68/2.00  
% 11.68/2.00  ------ Resolution Options
% 11.68/2.00  
% 11.68/2.00  --resolution_flag                       true
% 11.68/2.00  --res_lit_sel                           adaptive
% 11.68/2.00  --res_lit_sel_side                      none
% 11.68/2.00  --res_ordering                          kbo
% 11.68/2.00  --res_to_prop_solver                    active
% 11.68/2.00  --res_prop_simpl_new                    false
% 11.68/2.00  --res_prop_simpl_given                  true
% 11.68/2.00  --res_passive_queue_type                priority_queues
% 11.68/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/2.00  --res_passive_queues_freq               [15;5]
% 11.68/2.00  --res_forward_subs                      full
% 11.68/2.00  --res_backward_subs                     full
% 11.68/2.00  --res_forward_subs_resolution           true
% 11.68/2.00  --res_backward_subs_resolution          true
% 11.68/2.00  --res_orphan_elimination                true
% 11.68/2.00  --res_time_limit                        2.
% 11.68/2.00  --res_out_proof                         true
% 11.68/2.00  
% 11.68/2.00  ------ Superposition Options
% 11.68/2.00  
% 11.68/2.00  --superposition_flag                    true
% 11.68/2.00  --sup_passive_queue_type                priority_queues
% 11.68/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/2.00  --sup_passive_queues_freq               [1;4]
% 11.68/2.00  --demod_completeness_check              fast
% 11.68/2.00  --demod_use_ground                      true
% 11.68/2.00  --sup_to_prop_solver                    passive
% 11.68/2.00  --sup_prop_simpl_new                    true
% 11.68/2.00  --sup_prop_simpl_given                  true
% 11.68/2.00  --sup_fun_splitting                     false
% 11.68/2.00  --sup_smt_interval                      50000
% 11.68/2.00  
% 11.68/2.00  ------ Superposition Simplification Setup
% 11.68/2.00  
% 11.68/2.00  --sup_indices_passive                   []
% 11.68/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_full_bw                           [BwDemod]
% 11.68/2.00  --sup_immed_triv                        [TrivRules]
% 11.68/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_immed_bw_main                     []
% 11.68/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.68/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.68/2.00  
% 11.68/2.00  ------ Combination Options
% 11.68/2.00  
% 11.68/2.00  --comb_res_mult                         3
% 11.68/2.00  --comb_sup_mult                         2
% 11.68/2.00  --comb_inst_mult                        10
% 11.68/2.00  
% 11.68/2.00  ------ Debug Options
% 11.68/2.00  
% 11.68/2.00  --dbg_backtrace                         false
% 11.68/2.00  --dbg_dump_prop_clauses                 false
% 11.68/2.00  --dbg_dump_prop_clauses_file            -
% 11.68/2.00  --dbg_out_stat                          false
% 11.68/2.00  ------ Parsing...
% 11.68/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/2.00  ------ Proving...
% 11.68/2.00  ------ Problem Properties 
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  clauses                                 19
% 11.68/2.00  conjectures                             3
% 11.68/2.00  EPR                                     5
% 11.68/2.00  Horn                                    18
% 11.68/2.00  unary                                   7
% 11.68/2.00  binary                                  2
% 11.68/2.00  lits                                    43
% 11.68/2.00  lits eq                                 7
% 11.68/2.00  fd_pure                                 0
% 11.68/2.00  fd_pseudo                               0
% 11.68/2.00  fd_cond                                 0
% 11.68/2.00  fd_pseudo_cond                          1
% 11.68/2.00  AC symbols                              0
% 11.68/2.00  
% 11.68/2.00  ------ Input Options Time Limit: Unbounded
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  ------ 
% 11.68/2.00  Current options:
% 11.68/2.00  ------ 
% 11.68/2.00  
% 11.68/2.00  ------ Input Options
% 11.68/2.00  
% 11.68/2.00  --out_options                           all
% 11.68/2.00  --tptp_safe_out                         true
% 11.68/2.00  --problem_path                          ""
% 11.68/2.00  --include_path                          ""
% 11.68/2.00  --clausifier                            res/vclausify_rel
% 11.68/2.00  --clausifier_options                    --mode clausify
% 11.68/2.00  --stdin                                 false
% 11.68/2.00  --stats_out                             sel
% 11.68/2.00  
% 11.68/2.00  ------ General Options
% 11.68/2.00  
% 11.68/2.00  --fof                                   false
% 11.68/2.00  --time_out_real                         604.99
% 11.68/2.00  --time_out_virtual                      -1.
% 11.68/2.00  --symbol_type_check                     false
% 11.68/2.00  --clausify_out                          false
% 11.68/2.00  --sig_cnt_out                           false
% 11.68/2.00  --trig_cnt_out                          false
% 11.68/2.00  --trig_cnt_out_tolerance                1.
% 11.68/2.00  --trig_cnt_out_sk_spl                   false
% 11.68/2.00  --abstr_cl_out                          false
% 11.68/2.00  
% 11.68/2.00  ------ Global Options
% 11.68/2.00  
% 11.68/2.00  --schedule                              none
% 11.68/2.00  --add_important_lit                     false
% 11.68/2.00  --prop_solver_per_cl                    1000
% 11.68/2.00  --min_unsat_core                        false
% 11.68/2.00  --soft_assumptions                      false
% 11.68/2.00  --soft_lemma_size                       3
% 11.68/2.00  --prop_impl_unit_size                   0
% 11.68/2.00  --prop_impl_unit                        []
% 11.68/2.00  --share_sel_clauses                     true
% 11.68/2.00  --reset_solvers                         false
% 11.68/2.00  --bc_imp_inh                            [conj_cone]
% 11.68/2.00  --conj_cone_tolerance                   3.
% 11.68/2.00  --extra_neg_conj                        none
% 11.68/2.00  --large_theory_mode                     true
% 11.68/2.00  --prolific_symb_bound                   200
% 11.68/2.00  --lt_threshold                          2000
% 11.68/2.00  --clause_weak_htbl                      true
% 11.68/2.00  --gc_record_bc_elim                     false
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing Options
% 11.68/2.00  
% 11.68/2.00  --preprocessing_flag                    true
% 11.68/2.00  --time_out_prep_mult                    0.1
% 11.68/2.00  --splitting_mode                        input
% 11.68/2.00  --splitting_grd                         true
% 11.68/2.00  --splitting_cvd                         false
% 11.68/2.00  --splitting_cvd_svl                     false
% 11.68/2.00  --splitting_nvd                         32
% 11.68/2.00  --sub_typing                            true
% 11.68/2.00  --prep_gs_sim                           false
% 11.68/2.00  --prep_unflatten                        true
% 11.68/2.00  --prep_res_sim                          true
% 11.68/2.00  --prep_upred                            true
% 11.68/2.00  --prep_sem_filter                       exhaustive
% 11.68/2.00  --prep_sem_filter_out                   false
% 11.68/2.00  --pred_elim                             false
% 11.68/2.00  --res_sim_input                         true
% 11.68/2.00  --eq_ax_congr_red                       true
% 11.68/2.00  --pure_diseq_elim                       true
% 11.68/2.00  --brand_transform                       false
% 11.68/2.00  --non_eq_to_eq                          false
% 11.68/2.00  --prep_def_merge                        true
% 11.68/2.00  --prep_def_merge_prop_impl              false
% 11.68/2.00  --prep_def_merge_mbd                    true
% 11.68/2.00  --prep_def_merge_tr_red                 false
% 11.68/2.00  --prep_def_merge_tr_cl                  false
% 11.68/2.00  --smt_preprocessing                     true
% 11.68/2.00  --smt_ac_axioms                         fast
% 11.68/2.00  --preprocessed_out                      false
% 11.68/2.00  --preprocessed_stats                    false
% 11.68/2.00  
% 11.68/2.00  ------ Abstraction refinement Options
% 11.68/2.00  
% 11.68/2.00  --abstr_ref                             []
% 11.68/2.00  --abstr_ref_prep                        false
% 11.68/2.00  --abstr_ref_until_sat                   false
% 11.68/2.00  --abstr_ref_sig_restrict                funpre
% 11.68/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/2.00  --abstr_ref_under                       []
% 11.68/2.00  
% 11.68/2.00  ------ SAT Options
% 11.68/2.00  
% 11.68/2.00  --sat_mode                              false
% 11.68/2.00  --sat_fm_restart_options                ""
% 11.68/2.00  --sat_gr_def                            false
% 11.68/2.00  --sat_epr_types                         true
% 11.68/2.00  --sat_non_cyclic_types                  false
% 11.68/2.00  --sat_finite_models                     false
% 11.68/2.00  --sat_fm_lemmas                         false
% 11.68/2.00  --sat_fm_prep                           false
% 11.68/2.00  --sat_fm_uc_incr                        true
% 11.68/2.00  --sat_out_model                         small
% 11.68/2.00  --sat_out_clauses                       false
% 11.68/2.00  
% 11.68/2.00  ------ QBF Options
% 11.68/2.00  
% 11.68/2.00  --qbf_mode                              false
% 11.68/2.00  --qbf_elim_univ                         false
% 11.68/2.00  --qbf_dom_inst                          none
% 11.68/2.00  --qbf_dom_pre_inst                      false
% 11.68/2.00  --qbf_sk_in                             false
% 11.68/2.00  --qbf_pred_elim                         true
% 11.68/2.00  --qbf_split                             512
% 11.68/2.00  
% 11.68/2.00  ------ BMC1 Options
% 11.68/2.00  
% 11.68/2.00  --bmc1_incremental                      false
% 11.68/2.00  --bmc1_axioms                           reachable_all
% 11.68/2.00  --bmc1_min_bound                        0
% 11.68/2.00  --bmc1_max_bound                        -1
% 11.68/2.00  --bmc1_max_bound_default                -1
% 11.68/2.00  --bmc1_symbol_reachability              true
% 11.68/2.00  --bmc1_property_lemmas                  false
% 11.68/2.00  --bmc1_k_induction                      false
% 11.68/2.00  --bmc1_non_equiv_states                 false
% 11.68/2.00  --bmc1_deadlock                         false
% 11.68/2.00  --bmc1_ucm                              false
% 11.68/2.00  --bmc1_add_unsat_core                   none
% 11.68/2.00  --bmc1_unsat_core_children              false
% 11.68/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/2.00  --bmc1_out_stat                         full
% 11.68/2.00  --bmc1_ground_init                      false
% 11.68/2.00  --bmc1_pre_inst_next_state              false
% 11.68/2.00  --bmc1_pre_inst_state                   false
% 11.68/2.00  --bmc1_pre_inst_reach_state             false
% 11.68/2.00  --bmc1_out_unsat_core                   false
% 11.68/2.00  --bmc1_aig_witness_out                  false
% 11.68/2.00  --bmc1_verbose                          false
% 11.68/2.00  --bmc1_dump_clauses_tptp                false
% 11.68/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.68/2.00  --bmc1_dump_file                        -
% 11.68/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.68/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.68/2.00  --bmc1_ucm_extend_mode                  1
% 11.68/2.00  --bmc1_ucm_init_mode                    2
% 11.68/2.00  --bmc1_ucm_cone_mode                    none
% 11.68/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.68/2.00  --bmc1_ucm_relax_model                  4
% 11.68/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.68/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/2.00  --bmc1_ucm_layered_model                none
% 11.68/2.00  --bmc1_ucm_max_lemma_size               10
% 11.68/2.00  
% 11.68/2.00  ------ AIG Options
% 11.68/2.00  
% 11.68/2.00  --aig_mode                              false
% 11.68/2.00  
% 11.68/2.00  ------ Instantiation Options
% 11.68/2.00  
% 11.68/2.00  --instantiation_flag                    true
% 11.68/2.00  --inst_sos_flag                         false
% 11.68/2.00  --inst_sos_phase                        true
% 11.68/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/2.00  --inst_lit_sel_side                     num_symb
% 11.68/2.00  --inst_solver_per_active                1400
% 11.68/2.00  --inst_solver_calls_frac                1.
% 11.68/2.00  --inst_passive_queue_type               priority_queues
% 11.68/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/2.00  --inst_passive_queues_freq              [25;2]
% 11.68/2.00  --inst_dismatching                      true
% 11.68/2.00  --inst_eager_unprocessed_to_passive     true
% 11.68/2.00  --inst_prop_sim_given                   true
% 11.68/2.00  --inst_prop_sim_new                     false
% 11.68/2.00  --inst_subs_new                         false
% 11.68/2.00  --inst_eq_res_simp                      false
% 11.68/2.00  --inst_subs_given                       false
% 11.68/2.00  --inst_orphan_elimination               true
% 11.68/2.00  --inst_learning_loop_flag               true
% 11.68/2.00  --inst_learning_start                   3000
% 11.68/2.00  --inst_learning_factor                  2
% 11.68/2.00  --inst_start_prop_sim_after_learn       3
% 11.68/2.00  --inst_sel_renew                        solver
% 11.68/2.00  --inst_lit_activity_flag                true
% 11.68/2.00  --inst_restr_to_given                   false
% 11.68/2.00  --inst_activity_threshold               500
% 11.68/2.00  --inst_out_proof                        true
% 11.68/2.00  
% 11.68/2.00  ------ Resolution Options
% 11.68/2.00  
% 11.68/2.00  --resolution_flag                       true
% 11.68/2.00  --res_lit_sel                           adaptive
% 11.68/2.00  --res_lit_sel_side                      none
% 11.68/2.00  --res_ordering                          kbo
% 11.68/2.00  --res_to_prop_solver                    active
% 11.68/2.00  --res_prop_simpl_new                    false
% 11.68/2.00  --res_prop_simpl_given                  true
% 11.68/2.00  --res_passive_queue_type                priority_queues
% 11.68/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/2.00  --res_passive_queues_freq               [15;5]
% 11.68/2.00  --res_forward_subs                      full
% 11.68/2.00  --res_backward_subs                     full
% 11.68/2.00  --res_forward_subs_resolution           true
% 11.68/2.00  --res_backward_subs_resolution          true
% 11.68/2.00  --res_orphan_elimination                true
% 11.68/2.00  --res_time_limit                        2.
% 11.68/2.00  --res_out_proof                         true
% 11.68/2.00  
% 11.68/2.00  ------ Superposition Options
% 11.68/2.00  
% 11.68/2.00  --superposition_flag                    true
% 11.68/2.00  --sup_passive_queue_type                priority_queues
% 11.68/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/2.00  --sup_passive_queues_freq               [1;4]
% 11.68/2.00  --demod_completeness_check              fast
% 11.68/2.00  --demod_use_ground                      true
% 11.68/2.00  --sup_to_prop_solver                    passive
% 11.68/2.00  --sup_prop_simpl_new                    true
% 11.68/2.00  --sup_prop_simpl_given                  true
% 11.68/2.00  --sup_fun_splitting                     false
% 11.68/2.00  --sup_smt_interval                      50000
% 11.68/2.00  
% 11.68/2.00  ------ Superposition Simplification Setup
% 11.68/2.00  
% 11.68/2.00  --sup_indices_passive                   []
% 11.68/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.68/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_full_bw                           [BwDemod]
% 11.68/2.00  --sup_immed_triv                        [TrivRules]
% 11.68/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_immed_bw_main                     []
% 11.68/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.68/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.68/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.68/2.00  
% 11.68/2.00  ------ Combination Options
% 11.68/2.00  
% 11.68/2.00  --comb_res_mult                         3
% 11.68/2.00  --comb_sup_mult                         2
% 11.68/2.00  --comb_inst_mult                        10
% 11.68/2.00  
% 11.68/2.00  ------ Debug Options
% 11.68/2.00  
% 11.68/2.00  --dbg_backtrace                         false
% 11.68/2.00  --dbg_dump_prop_clauses                 false
% 11.68/2.00  --dbg_dump_prop_clauses_file            -
% 11.68/2.00  --dbg_out_stat                          false
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  ------ Proving...
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  % SZS status Theorem for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  fof(f13,axiom,(
% 11.68/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f55,plain,(
% 11.68/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.68/2.00    inference(cnf_transformation,[],[f13])).
% 11.68/2.00  
% 11.68/2.00  fof(f2,axiom,(
% 11.68/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f40,plain,(
% 11.68/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f2])).
% 11.68/2.00  
% 11.68/2.00  fof(f1,axiom,(
% 11.68/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f32,plain,(
% 11.68/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/2.00    inference(nnf_transformation,[],[f1])).
% 11.68/2.00  
% 11.68/2.00  fof(f33,plain,(
% 11.68/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/2.00    inference(flattening,[],[f32])).
% 11.68/2.00  
% 11.68/2.00  fof(f39,plain,(
% 11.68/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f33])).
% 11.68/2.00  
% 11.68/2.00  fof(f16,conjecture,(
% 11.68/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f17,negated_conjecture,(
% 11.68/2.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 11.68/2.00    inference(negated_conjecture,[],[f16])).
% 11.68/2.00  
% 11.68/2.00  fof(f30,plain,(
% 11.68/2.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.68/2.00    inference(ennf_transformation,[],[f17])).
% 11.68/2.00  
% 11.68/2.00  fof(f31,plain,(
% 11.68/2.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.68/2.00    inference(flattening,[],[f30])).
% 11.68/2.00  
% 11.68/2.00  fof(f35,plain,(
% 11.68/2.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 11.68/2.00    introduced(choice_axiom,[])).
% 11.68/2.00  
% 11.68/2.00  fof(f36,plain,(
% 11.68/2.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 11.68/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f35])).
% 11.68/2.00  
% 11.68/2.00  fof(f60,plain,(
% 11.68/2.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 11.68/2.00    inference(cnf_transformation,[],[f36])).
% 11.68/2.00  
% 11.68/2.00  fof(f3,axiom,(
% 11.68/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f41,plain,(
% 11.68/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f3])).
% 11.68/2.00  
% 11.68/2.00  fof(f4,axiom,(
% 11.68/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f42,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f4])).
% 11.68/2.00  
% 11.68/2.00  fof(f5,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f43,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f5])).
% 11.68/2.00  
% 11.68/2.00  fof(f6,axiom,(
% 11.68/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f44,plain,(
% 11.68/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f6])).
% 11.68/2.00  
% 11.68/2.00  fof(f61,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f43,f44])).
% 11.68/2.00  
% 11.68/2.00  fof(f62,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f42,f61])).
% 11.68/2.00  
% 11.68/2.00  fof(f63,plain,(
% 11.68/2.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f41,f62])).
% 11.68/2.00  
% 11.68/2.00  fof(f66,plain,(
% 11.68/2.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 11.68/2.00    inference(definition_unfolding,[],[f60,f63,f63])).
% 11.68/2.00  
% 11.68/2.00  fof(f10,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f21,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 11.68/2.00    inference(ennf_transformation,[],[f10])).
% 11.68/2.00  
% 11.68/2.00  fof(f22,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 11.68/2.00    inference(flattening,[],[f21])).
% 11.68/2.00  
% 11.68/2.00  fof(f51,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X1) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f22])).
% 11.68/2.00  
% 11.68/2.00  fof(f8,axiom,(
% 11.68/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f19,plain,(
% 11.68/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.68/2.00    inference(ennf_transformation,[],[f8])).
% 11.68/2.00  
% 11.68/2.00  fof(f34,plain,(
% 11.68/2.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.68/2.00    inference(nnf_transformation,[],[f19])).
% 11.68/2.00  
% 11.68/2.00  fof(f46,plain,(
% 11.68/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f34])).
% 11.68/2.00  
% 11.68/2.00  fof(f14,axiom,(
% 11.68/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f26,plain,(
% 11.68/2.00    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.68/2.00    inference(ennf_transformation,[],[f14])).
% 11.68/2.00  
% 11.68/2.00  fof(f27,plain,(
% 11.68/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.68/2.00    inference(flattening,[],[f26])).
% 11.68/2.00  
% 11.68/2.00  fof(f56,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f27])).
% 11.68/2.00  
% 11.68/2.00  fof(f9,axiom,(
% 11.68/2.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f20,plain,(
% 11.68/2.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.68/2.00    inference(ennf_transformation,[],[f9])).
% 11.68/2.00  
% 11.68/2.00  fof(f48,plain,(
% 11.68/2.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f20])).
% 11.68/2.00  
% 11.68/2.00  fof(f12,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f24,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.68/2.00    inference(ennf_transformation,[],[f12])).
% 11.68/2.00  
% 11.68/2.00  fof(f25,plain,(
% 11.68/2.00    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 11.68/2.00    inference(flattening,[],[f24])).
% 11.68/2.00  
% 11.68/2.00  fof(f53,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f25])).
% 11.68/2.00  
% 11.68/2.00  fof(f38,plain,(
% 11.68/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.68/2.00    inference(cnf_transformation,[],[f33])).
% 11.68/2.00  
% 11.68/2.00  fof(f67,plain,(
% 11.68/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.68/2.00    inference(equality_resolution,[],[f38])).
% 11.68/2.00  
% 11.68/2.00  fof(f7,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f18,plain,(
% 11.68/2.00    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 11.68/2.00    inference(ennf_transformation,[],[f7])).
% 11.68/2.00  
% 11.68/2.00  fof(f45,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f18])).
% 11.68/2.00  
% 11.68/2.00  fof(f64,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f45,f62])).
% 11.68/2.00  
% 11.68/2.00  fof(f11,axiom,(
% 11.68/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f23,plain,(
% 11.68/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.68/2.00    inference(ennf_transformation,[],[f11])).
% 11.68/2.00  
% 11.68/2.00  fof(f52,plain,(
% 11.68/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f23])).
% 11.68/2.00  
% 11.68/2.00  fof(f47,plain,(
% 11.68/2.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f34])).
% 11.68/2.00  
% 11.68/2.00  fof(f15,axiom,(
% 11.68/2.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 11.68/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/2.00  
% 11.68/2.00  fof(f28,plain,(
% 11.68/2.00    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.68/2.00    inference(ennf_transformation,[],[f15])).
% 11.68/2.00  
% 11.68/2.00  fof(f29,plain,(
% 11.68/2.00    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.68/2.00    inference(flattening,[],[f28])).
% 11.68/2.00  
% 11.68/2.00  fof(f57,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.68/2.00    inference(cnf_transformation,[],[f29])).
% 11.68/2.00  
% 11.68/2.00  fof(f65,plain,(
% 11.68/2.00    ( ! [X2,X0,X1] : (k3_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.68/2.00    inference(definition_unfolding,[],[f57,f62,f62])).
% 11.68/2.00  
% 11.68/2.00  fof(f59,plain,(
% 11.68/2.00    v1_funct_1(sK1)),
% 11.68/2.00    inference(cnf_transformation,[],[f36])).
% 11.68/2.00  
% 11.68/2.00  fof(f58,plain,(
% 11.68/2.00    v1_relat_1(sK1)),
% 11.68/2.00    inference(cnf_transformation,[],[f36])).
% 11.68/2.00  
% 11.68/2.00  cnf(c_255,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1122,plain,
% 11.68/2.00      ( X0 != X1 | X0 = k7_relat_1(sK1,X2) | k7_relat_1(sK1,X2) != X1 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_255]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1929,plain,
% 11.68/2.00      ( X0 != k7_relat_1(X1,X2)
% 11.68/2.00      | X0 = k7_relat_1(sK1,X3)
% 11.68/2.00      | k7_relat_1(sK1,X3) != k7_relat_1(X1,X2) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1122]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_9677,plain,
% 11.68/2.00      ( X0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | X0 = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1929]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_40571,plain,
% 11.68/2.00      ( k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | k1_xboole_0 = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_9677]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_254,plain,( X0 = X0 ),theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2958,plain,
% 11.68/2.00      ( X0 != X1 | X1 = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_255,c_254]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_13,plain,
% 11.68/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4561,plain,
% 11.68/2.00      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2958,c_13]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_264,plain,
% 11.68/2.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 11.68/2.00      theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2961,plain,
% 11.68/2.00      ( X0 != X1 | X2 != k2_relat_1(X1) | k2_relat_1(X0) = X2 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_255,c_264]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_28418,plain,
% 11.68/2.00      ( X0 != k1_xboole_0 | k2_relat_1(X0) = k1_xboole_0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_4561,c_2961]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2952,plain,
% 11.68/2.00      ( X0 != k1_xboole_0 | k2_relat_1(k1_xboole_0) = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_255,c_13]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4574,plain,
% 11.68/2.00      ( X0 = k2_relat_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2958,c_2952]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_256,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/2.00      theory(equality) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2997,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_256,c_254]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4591,plain,
% 11.68/2.00      ( r1_tarski(X0,X1)
% 11.68/2.00      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
% 11.68/2.00      | X0 != k1_xboole_0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_4574,c_2997]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_3645,plain,
% 11.68/2.00      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 11.68/2.00      | ~ r1_tarski(k1_xboole_0,X0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2997,c_13]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_3,plain,
% 11.68/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_3762,plain,
% 11.68/2.00      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
% 11.68/2.00      inference(global_propositional_subsumption,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_3645,c_3]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_9609,plain,
% 11.68/2.00      ( r1_tarski(X0,X1) | X0 != k1_xboole_0 ),
% 11.68/2.00      inference(forward_subsumption_resolution,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_4591,c_3762]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_33793,plain,
% 11.68/2.00      ( r1_tarski(k2_relat_1(X0),X1) | X0 != k1_xboole_0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_28418,c_9609]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_28376,plain,
% 11.68/2.00      ( X0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_4561,c_255]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_0,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.68/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2942,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_255,c_0]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_11443,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.68/2.00      | ~ r1_tarski(k1_xboole_0,X0)
% 11.68/2.00      | X0 = k2_relat_1(k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_2942,c_13]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_14712,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k2_relat_1(k1_xboole_0) ),
% 11.68/2.00      inference(global_propositional_subsumption,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_11443,c_3]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_32961,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_28376,c_14712]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_33305,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_32961,c_2958]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_34274,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(k2_relat_1(X0),X1) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_33793,c_33305]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_17,negated_conjecture,
% 11.68/2.00      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 11.68/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_35350,plain,
% 11.68/2.00      ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
% 11.68/2.00      inference(resolution,[status(thm)],[c_34274,c_17]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1638,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1)
% 11.68/2.00      | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X2)
% 11.68/2.00      | X2 != X1
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_256]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4009,plain,
% 11.68/2.00      ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.68/2.00      | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X1)
% 11.68/2.00      | X1 != X0
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_10497,plain,
% 11.68/2.00      ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.68/2.00      | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_4009]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_27120,plain,
% 11.68/2.00      ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k1_xboole_0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_10497]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_8,plain,
% 11.68/2.00      ( ~ v4_relat_1(X0,X1)
% 11.68/2.00      | v4_relat_1(k7_relat_1(X0,X2),X1)
% 11.68/2.00      | ~ v1_relat_1(X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_954,plain,
% 11.68/2.00      ( v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
% 11.68/2.00      | ~ v4_relat_1(sK1,k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_6990,plain,
% 11.68/2.00      ( v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | ~ v4_relat_1(sK1,k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_954]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1007,plain,
% 11.68/2.00      ( X0 != X1
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != X1
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_255]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1650,plain,
% 11.68/2.00      ( X0 != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1007]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_6150,plain,
% 11.68/2.00      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1650]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5615,plain,
% 11.68/2.00      ( k1_xboole_0 = k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_254]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1865,plain,
% 11.68/2.00      ( X0 != X1
% 11.68/2.00      | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_255]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4414,plain,
% 11.68/2.00      ( X0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X2)),k1_relat_1(sK1))
% 11.68/2.00      | X0 != k1_xboole_0
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X2)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1865]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5614,plain,
% 11.68/2.00      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) != k1_xboole_0
% 11.68/2.00      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1))
% 11.68/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_4414]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5616,plain,
% 11.68/2.00      ( k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
% 11.68/2.00      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_5614]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_6,plain,
% 11.68/2.00      ( ~ v4_relat_1(X0,X1)
% 11.68/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.68/2.00      | ~ v1_relat_1(X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1268,plain,
% 11.68/2.00      ( ~ v4_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
% 11.68/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_3419,plain,
% 11.68/2.00      ( ~ v4_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 11.68/2.00      | r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1268]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_15,plain,
% 11.68/2.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.68/2.00      | ~ v1_relat_1(X0)
% 11.68/2.00      | k7_relat_1(X0,X1) = X0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_833,plain,
% 11.68/2.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
% 11.68/2.00      | ~ v1_relat_1(k7_relat_1(sK1,X0))
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,X0) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2189,plain,
% 11.68/2.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)
% 11.68/2.00      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_833]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_3418,plain,
% 11.68/2.00      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_2189]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_7,plain,
% 11.68/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.68/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_727,plain,
% 11.68/2.00      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2592,plain,
% 11.68/2.00      ( v1_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_727]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_12,plain,
% 11.68/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.68/2.00      | ~ v1_relat_1(X2)
% 11.68/2.00      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 11.68/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1496,plain,
% 11.68/2.00      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(X2)
% 11.68/2.00      | k7_relat_1(k7_relat_1(X2,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2078,plain,
% 11.68/2.00      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(sK1)
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X1)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1496]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2080,plain,
% 11.68/2.00      ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(sK1)
% 11.68/2.00      | k7_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_2078]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1,plain,
% 11.68/2.00      ( r1_tarski(X0,X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1633,plain,
% 11.68/2.00      ( r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1001,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = X0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1632,plain,
% 11.68/2.00      ( ~ r1_tarski(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1001]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1059,plain,
% 11.68/2.00      ( r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_770,plain,
% 11.68/2.00      ( ~ r1_tarski(X0,X1)
% 11.68/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.68/2.00      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 11.68/2.00      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != X0 ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_256]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_934,plain,
% 11.68/2.00      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)
% 11.68/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.68/2.00      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 11.68/2.00      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_770]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_1058,plain,
% 11.68/2.00      ( ~ r1_tarski(k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
% 11.68/2.00      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 11.68/2.00      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
% 11.68/2.00      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_934]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_4,plain,
% 11.68/2.00      ( r2_hidden(X0,X1)
% 11.68/2.00      | r2_hidden(X2,X1)
% 11.68/2.00      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
% 11.68/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_942,plain,
% 11.68/2.00      ( r2_hidden(X0,k1_relat_1(sK1))
% 11.68/2.00      | r2_hidden(X1,k1_relat_1(sK1))
% 11.68/2.00      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_relat_1(sK1)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_944,plain,
% 11.68/2.00      ( r2_hidden(sK0,k1_relat_1(sK1))
% 11.68/2.00      | r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_942]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_11,plain,
% 11.68/2.00      ( ~ v1_relat_1(X0)
% 11.68/2.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.68/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_760,plain,
% 11.68/2.00      ( ~ v1_relat_1(sK1)
% 11.68/2.00      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_935,plain,
% 11.68/2.00      ( ~ v1_relat_1(sK1)
% 11.68/2.00      | k2_relat_1(k7_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_760]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_870,plain,
% 11.68/2.00      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_5,plain,
% 11.68/2.00      ( v4_relat_1(X0,X1)
% 11.68/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.68/2.00      | ~ v1_relat_1(X0) ),
% 11.68/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_755,plain,
% 11.68/2.00      ( v4_relat_1(sK1,X0)
% 11.68/2.00      | ~ r1_tarski(k1_relat_1(sK1),X0)
% 11.68/2.00      | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_869,plain,
% 11.68/2.00      ( v4_relat_1(sK1,k1_relat_1(sK1))
% 11.68/2.00      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_relat_1(sK1) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_755]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_16,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.68/2.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 11.68/2.00      | ~ v1_funct_1(X1)
% 11.68/2.00      | ~ v1_relat_1(X1)
% 11.68/2.00      | k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X0)) ),
% 11.68/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_797,plain,
% 11.68/2.00      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 11.68/2.00      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_funct_1(sK1)
% 11.68/2.00      | ~ v1_relat_1(sK1)
% 11.68/2.00      | k3_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k3_enumset1(X1,X1,X1,X1,X0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_16]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_799,plain,
% 11.68/2.00      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 11.68/2.00      | ~ v1_funct_1(sK1)
% 11.68/2.00      | ~ v1_relat_1(sK1)
% 11.68/2.00      | k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_797]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_18,negated_conjecture,
% 11.68/2.00      ( v1_funct_1(sK1) ),
% 11.68/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_19,negated_conjecture,
% 11.68/2.00      ( v1_relat_1(sK1) ),
% 11.68/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(contradiction,plain,
% 11.68/2.00      ( $false ),
% 11.68/2.00      inference(minisat,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_40571,c_35350,c_27120,c_6990,c_6150,c_5615,c_5616,
% 11.68/2.00                 c_3419,c_3418,c_2592,c_2080,c_1633,c_1632,c_1059,c_1058,
% 11.68/2.00                 c_944,c_935,c_870,c_869,c_799,c_17,c_18,c_19]) ).
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  ------                               Statistics
% 11.68/2.00  
% 11.68/2.00  ------ Selected
% 11.68/2.00  
% 11.68/2.00  total_time:                             1.279
% 11.68/2.00  
%------------------------------------------------------------------------------
